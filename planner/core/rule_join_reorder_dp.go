// Copyright 2018 PingCAP, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// See the License for the specific language governing permissions and
// limitations under the License.

package core

import (
	"math/bits"

	"github.com/pingcap/tidb/expression"
	"github.com/pingcap/tidb/parser/ast"
)

type joinReorderDPSolver struct {
	*baseSingleGroupJoinOrderSolver
	newJoin func(lChild, rChild LogicalPlan, eqConds []*expression.ScalarFunction, otherConds []expression.Expression) LogicalPlan
}

type joinGroupEqEdge struct {
	nodeIDs []int
	edge    *expression.ScalarFunction
}

type joinGroupNonEqEdge struct {
	nodeIDs    []int
	nodeIDMask uint
	expr       expression.Expression
}

// solve reorder join group and create new LogicalPlan
//
// TODO: Need more test
func (s *joinReorderDPSolver) solve(joinGroup []LogicalPlan, eqConds []expression.Expression) (LogicalPlan, error) {
	for _, join := range joinGroup {
		s.curJoinGroup = append(s.curJoinGroup, &jrNode{
			p:       join,
			cumCost: s.baseNodeCumCost(join),
		})
	}

	// Build eq graph
	eqEdges := make([]joinGroupEqEdge, 0, len(eqConds))
	eqGraph := make([][]int, len(joinGroup))
	for _, eqCond := range eqConds {
		sf := eqCond.(*expression.ScalarFunction)
		args := sf.GetArgs()
		lcol := args[0].(*expression.Column)
		rcol := args[1].(*expression.Column)
		lNodeID, err := findNodeIndexInGroup(joinGroup, lcol)
		if err != nil {
			return nil, err
		}
		rNodeID, err := findNodeIndexInGroup(joinGroup, rcol)
		if err != nil {
			return nil, err
		}

		eqEdges = append(eqEdges, joinGroupEqEdge{
			nodeIDs: []int{lNodeID, rNodeID},
			edge:    sf,
		})
		eqGraph[lNodeID] = append(eqGraph[lNodeID], rNodeID)
		eqGraph[rNodeID] = append(eqGraph[rNodeID], lNodeID)
	}

	// Loop connected graphs
	newJoinGroup := make([]LogicalPlan, 0)
	visitedJoinNodeIDs := make([]bool, len(s.curJoinGroup))
	for i := range s.curJoinGroup {
		if visitedJoinNodeIDs[i] {
			continue
		}

		nodeIDs := extractConnectedNodes(eqGraph, i, visitedJoinNodeIDs)

		// Find best plan in connected graph
		join, err := s.findBestPlan(nodeIDs, eqEdges)
		if err != nil {
			return nil, err
		}
		newJoinGroup = append(newJoinGroup, join)
	}

	// TODO: Here I did not consider otherConds
	return s.makeBushyJoin(newJoinGroup, s.otherConds), nil
}

// extractConnectedNodes extract a connected graph from start node
// and update vistedJoinNodeIDs
func extractConnectedNodes(graph [][]int, start int, visitedJoinNodeIDs []bool) (nodeIDs []int) {
	if visitedJoinNodeIDs[start] {
		return
	}
	visitedJoinNodeIDs[start] = true

	queue := make([]int, 1)
	queue[0] = start

	for len(queue) > 0 {
		node := queue[0]
		nodeIDs = append(nodeIDs, node)
		queue = queue[1:]

		for _, nearNode := range graph[node] {
			if visitedJoinNodeIDs[nearNode] {
				continue
			}

			visitedJoinNodeIDs[nearNode] = true
			queue = append(queue, nearNode)
		}
	}

	return
}

// findBestPlan find best plan based on db. nodeIDs must be a connect graph.
//
// TODO: Need more test
func (s *joinReorderDPSolver) findBestPlan(nodeIDs []int, eqEdges []joinGroupEqEdge) (LogicalPlan, error) {
	bestPlan := make([]*jrNode, 1<<len(nodeIDs))
	globalID2Mask := make(map[int]uint32) // TODO: Supports up to 32 nodes?
	for id, globalID := range nodeIDs {
		bestPlan[1<<id] = s.curJoinGroup[globalID]
		globalID2Mask[globalID] = 1 << id
	}

	for group := uint32(1); group < (1 << len(nodeIDs)); group++ {
		// The leaf nodes are predefined
		if bits.OnesCount32(group) == 1 {
			continue
		}

		// Loop sub groups
		for sub := (group - 1) & group; sub > 0; sub = (sub - 1) & group {
			remain := group ^ sub

			if bestPlan[sub] == nil || bestPlan[remain] == nil {
				// sub or remain is not connectivity graph
				continue
			}

			// Find used edges
			usedEdges := make([]joinGroupEqEdge, 0)
			for _, edge := range eqEdges {
				lNodeMask := globalID2Mask[edge.nodeIDs[0]]
				rNodeMask := globalID2Mask[edge.nodeIDs[1]]
				if (sub&lNodeMask > 0 && remain&rNodeMask > 0) || (sub&rNodeMask > 0 && remain&lNodeMask > 0) {
					usedEdges = append(usedEdges, edge)
				}
			}
			if len(usedEdges) == 0 {
				// sub is not connect to remain
				continue
			}

			// Generate plan and calc cost
			plan, err := s.newJoinWithEdge(bestPlan[remain].p, bestPlan[sub].p, usedEdges, nil)
			if err != nil {
				return nil, err
			}
			cost := s.calcJoinCumCost(plan, bestPlan[remain], bestPlan[sub])

			// f[group] = min{join{f[sub], f[group ^ sub])}
			if bestPlan[group] == nil {
				bestPlan[group] = &jrNode{
					p:       plan,
					cumCost: cost,
				}
			} else if bestPlan[group].cumCost > cost {
				bestPlan[group].p = plan
				bestPlan[group].cumCost = cost
			}
		}
	}

	return bestPlan[len(bestPlan)-1].p, nil
}

func (s *joinReorderDPSolver) newJoinWithEdge(leftPlan, rightPlan LogicalPlan, edges []joinGroupEqEdge, otherConds []expression.Expression) (LogicalPlan, error) {
	var eqConds []*expression.ScalarFunction
	for _, edge := range edges {
		lCol := edge.edge.GetArgs()[0].(*expression.Column)
		rCol := edge.edge.GetArgs()[1].(*expression.Column)
		if leftPlan.Schema().Contains(lCol) {
			eqConds = append(eqConds, edge.edge)
		} else {
			newSf := expression.NewFunctionInternal(s.ctx, ast.EQ, edge.edge.GetType(), rCol, lCol).(*expression.ScalarFunction)
			eqConds = append(eqConds, newSf)
		}
	}
	join := s.newJoin(leftPlan, rightPlan, eqConds, otherConds)
	_, err := join.recursiveDeriveStats()
	return join, err
}

// Make cartesian join as bushy tree.
func (s *joinReorderDPSolver) makeBushyJoin(cartesianJoinGroup []LogicalPlan, otherConds []expression.Expression) LogicalPlan {
	for len(cartesianJoinGroup) > 1 {
		resultJoinGroup := make([]LogicalPlan, 0, len(cartesianJoinGroup))
		for i := 0; i < len(cartesianJoinGroup); i += 2 {
			if i+1 == len(cartesianJoinGroup) {
				resultJoinGroup = append(resultJoinGroup, cartesianJoinGroup[i])
				break
			}
			// TODO:Since the other condition may involve more than two tables, e.g. t1.a = t2.b+t3.c.
			//  So We'll need a extra stage to deal with it.
			// Currently, we just add it when building cartesianJoinGroup.
			mergedSchema := expression.MergeSchema(cartesianJoinGroup[i].Schema(), cartesianJoinGroup[i+1].Schema())
			var usedOtherConds []expression.Expression
			otherConds, usedOtherConds = expression.FilterOutInPlace(otherConds, func(expr expression.Expression) bool {
				return expression.ExprFromSchema(expr, mergedSchema)
			})
			resultJoinGroup = append(resultJoinGroup, s.newJoin(cartesianJoinGroup[i], cartesianJoinGroup[i+1], nil, usedOtherConds))
		}
		cartesianJoinGroup = resultJoinGroup
	}
	return cartesianJoinGroup[0]
}

func findNodeIndexInGroup(group []LogicalPlan, col *expression.Column) (int, error) {
	for i, plan := range group {
		if plan.Schema().Contains(col) {
			return i, nil
		}
	}
	return -1, ErrUnknownColumn.GenWithStackByArgs(col, "JOIN REORDER RULE")
}
