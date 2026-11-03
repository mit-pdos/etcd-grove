// Copyright 2026 The etcd Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package raft

// The panic of removed_candidate_test.go, end to end through the public RawNode API
// (needs leaderlag_test.go, whose harness it uses). C0 = {1,2,3}; node 1 leads and
// commits "remove 3"; node 3's application calls Advance for that Ready before it
// calls ApplyConfChange (doc.go step 4). Node 3 campaigns (no conf change in
// (applied, committed]), then its application applies the removal: node 3 is a
// candidate outside its configuration {1,2}. Nodes 1 and 2 grant the vote (node 3's
// log is up to date) and node 3's becomeLeader dereferences its missing Progress.
//
// The test PASSES when the panic is reproduced.

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

func TestRemovedCandidateWinsAndPanicsRawNode(t *testing.T) {
	c := &llCluster{t: t, drop: func(pb.Message) bool { return false }, nodes: map[uint64]*llNode{
		1: newLLNode(t, 1, []uint64{1, 2, 3}, false),
		2: newLLNode(t, 2, []uint64{1, 2, 3}, false),
		3: newLLNode(t, 3, []uint64{1, 2, 3}, true /* lagging application */),
	}}
	if err := c.nodes[1].rn.Campaign(); err != nil {
		t.Fatal(err)
	}
	c.stabilize()
	if err := c.nodes[1].rn.ProposeConfChange(pb.ConfChange{Type: pb.ConfChangeRemoveNode, NodeId: 3}); err != nil {
		t.Fatal(err)
	}
	c.stabilize()
	if len(c.nodes[3].pendingCC) != 1 {
		t.Fatalf("node 3 should hold its removal back, holds %d conf changes", len(c.nodes[3].pendingCC))
	}
	if err := c.nodes[3].rn.Campaign(); err != nil {
		t.Fatal(err)
	}
	if st := c.nodes[3].rn.BasicStatus().RaftState; st != StateCandidate {
		t.Fatalf("node 3 did not campaign: %v", st)
	}
	// The application finishes applying: node 3 is removed, and stays a candidate.
	for _, cc := range c.nodes[3].pendingCC {
		c.nodes[3].rn.ApplyConfChange(cc)
	}
	t.Logf("node 3: %v, config %v", c.nodes[3].rn.BasicStatus().RaftState, c.cfg(3))
	defer func() {
		if e := recover(); e != nil {
			t.Logf("PANIC reproduced: %v", e)
			return
		}
		t.Fatalf("no panic: node 3 is %v", c.nodes[3].rn.BasicStatus().RaftState)
	}()
	c.stabilize()
}
