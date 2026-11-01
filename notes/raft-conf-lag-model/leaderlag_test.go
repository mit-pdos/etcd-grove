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

// Reproduction of a safety violation: an application that calls Advance before
// ApplyConfChange -- which doc.go allows ("4. Call Node.Advance() ... This may be
// done at any time after step 1", where applying the committed entries, including
// ApplyConfChange, is step 3; node.go says the same of Advance) -- lets two
// different entries be committed at the same index.
//
// The "leader lag" execution. C0 = {1,2,3}; node 1 leads term 1.
//   - Node 1 commits C1 = "add 4" (index 2) with {1,2}. Its application calls
//     Advance for that Ready but has not yet called ApplyConfChange for C1 (it is
//     still "applying"), so raft's applied index is 2 while node 1 is still on C0.
//   - Node 1 proposes C2 = "remove 2" (index 3). The leader's guard
//     `pendingConfIndex > applied` (raft.go) is 2 > 2 = false: accepted. C2 commits
//     under C0 with {1,2}.
//   - Node 3 receives indices 1-3 with Commit = 3 and applies both changes
//     (ApplyConfChange, faithfully, before Advance): its configuration is {1,3,4}.
//   - Node 1 (still on C0) commits x at index 4 with {1,2}; node 3 never sees it.
//   - Partition {1,2} | {3,4}. Node 3 campaigns (applied = committed = 3, so no
//     unapplied conf change blocks it), wins term 2 with {3,4} -- a majority of
//     {1,3,4} -- and commits its own entries at index 4 (its empty leader entry)
//     and 5 with {3,4}.
//
// Everything is driven through the public RawNode API (Campaign, Propose,
// ProposeConfChange, Ready, Advance, ApplyConfChange, Step) and MemoryStorage,
// with synchronous storage writes; messages are routed by hand. No internal
// shortcut is used: the only "fault" is node 1's application calling Advance for
// a Ready before it has called ApplyConfChange for that Ready's conf changes, plus
// a network partition. Node 4 starts as a joining node does (empty storage, no
// configuration) and learns the log from node 3 once node 3 leads.
//
// The test PASSES when the violation is reproduced: it asserts that nodes 1 and 3
// both report (in Ready.CommittedEntries) a committed entry at index 4 and that
// the two entries differ. If raft is fixed (or the documentation's permission is
// withdrawn and the guards change), the assertion fails.

import (
	"bytes"
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

type llNode struct {
	id      uint64
	rn      *RawNode
	st      *MemoryStorage
	lagging bool // Advance before ApplyConfChange (node 1's application)
	// conf changes committed and Advanced past but not yet ApplyConfChange'd:
	// the lagging application is "still applying" them.
	pendingCC []pb.ConfChangeI
	committed map[uint64]pb.Entry // what the application was told is committed
}

type llCluster struct {
	t     *testing.T
	nodes map[uint64]*llNode
	queue []pb.Message
	// drop reports whether a message is lost (partition).
	drop func(m pb.Message) bool
}

func newLLNode(t *testing.T, id uint64, voters []uint64, lagging bool) *llNode {
	st := NewMemoryStorage()
	if len(voters) > 0 {
		// Bootstrap the initial configuration through a snapshot, as
		// RawNode.Bootstrap-style setups do (index 0: the log starts empty).
		if err := st.ApplySnapshot(pb.Snapshot{Metadata: pb.SnapshotMetadata{
			ConfState: pb.ConfState{Voters: voters},
		}}); err != nil {
			t.Fatal(err)
		}
	}
	rn, err := NewRawNode(&Config{
		ID:              id,
		ElectionTick:    10,
		HeartbeatTick:   1,
		Storage:         st,
		MaxSizePerMsg:   noLimit,
		MaxInflightMsgs: 256,
		Logger:          discardLogger,
	})
	if err != nil {
		t.Fatal(err)
	}
	return &llNode{id: id, rn: rn, st: st, lagging: lagging, committed: map[uint64]pb.Entry{}}
}

func decodeCC(t *testing.T, e pb.Entry) pb.ConfChangeI {
	switch e.Type {
	case pb.EntryConfChange:
		var cc pb.ConfChange
		if err := cc.Unmarshal(e.Data); err != nil {
			t.Fatal(err)
		}
		return cc
	case pb.EntryConfChangeV2:
		var cc pb.ConfChangeV2
		if err := cc.Unmarshal(e.Data); err != nil {
			t.Fatal(err)
		}
		return cc
	}
	return nil
}

// handleReady processes one Ready of n the way doc.go describes, with
// synchronous storage: persist, send, apply, Advance. A lagging node calls
// Advance before ApplyConfChange (doc.go step 4 "may be done at any time after
// step 1").
func (c *llCluster) handleReady(n *llNode) {
	rd := n.rn.Ready()
	if !IsEmptyHardState(rd.HardState) {
		if err := n.st.SetHardState(rd.HardState); err != nil {
			c.t.Fatal(err)
		}
	}
	if err := n.st.Append(rd.Entries); err != nil {
		c.t.Fatal(err)
	}
	c.queue = append(c.queue, rd.Messages...)
	var ccs []pb.ConfChangeI
	for _, e := range rd.CommittedEntries {
		if old, ok := n.committed[e.Index]; ok && (old.Term != e.Term || !bytes.Equal(old.Data, e.Data)) {
			c.t.Fatalf("node %d: index %d committed twice differently", n.id, e.Index)
		}
		n.committed[e.Index] = e
		if cc := decodeCC(c.t, e); cc != nil {
			ccs = append(ccs, cc)
		}
	}
	if n.lagging {
		// Step 4 before step 3 finishes: Advance now; the conf changes are
		// still being applied (ApplyConfChange comes later, see pendingCC).
		n.rn.Advance(rd)
		n.pendingCC = append(n.pendingCC, ccs...)
		return
	}
	for _, cc := range ccs {
		n.rn.ApplyConfChange(cc)
	}
	n.rn.Advance(rd)
}

// stabilize runs Readys and delivers messages (except dropped ones) until quiet.
func (c *llCluster) stabilize() {
	for i := 0; i < 10000; i++ {
		progress := false
		for id := uint64(1); id <= 4; id++ {
			if n := c.nodes[id]; n != nil && n.rn.HasReady() {
				c.handleReady(n)
				progress = true
			}
		}
		msgs := c.queue
		c.queue = nil
		for _, m := range msgs {
			to := c.nodes[m.To]
			if to == nil || c.drop(m) {
				continue
			}
			progress = true
			_ = to.rn.Step(m)
		}
		if !progress {
			return
		}
	}
	c.t.Fatal("did not stabilize")
}

func (c *llCluster) cfg(id uint64) string {
	return c.nodes[id].rn.Status().Config.String() // the configuration in use
}

func TestAdvanceBeforeApplyConfChangeLeaderLag(t *testing.T) {
	c := &llCluster{t: t, nodes: map[uint64]*llNode{
		1: newLLNode(t, 1, []uint64{1, 2, 3}, true /* lagging application */),
		2: newLLNode(t, 2, []uint64{1, 2, 3}, false),
		3: newLLNode(t, 3, []uint64{1, 2, 3}, false),
		4: newLLNode(t, 4, nil, false), // joining node: empty storage, no config
	}}
	isolate := func(ids ...uint64) func(pb.Message) bool {
		in := map[uint64]bool{}
		for _, id := range ids {
			in[id] = true
		}
		return func(m pb.Message) bool { return in[m.From] != in[m.To] }
	}

	// Phase 1: {1,2,3} connected (node 4 is unknown to node 1's C0, and hears
	// nothing). Node 1 leads term 1 and commits its empty entry at index 1.
	c.drop = func(pb.Message) bool { return false }
	if err := c.nodes[1].rn.Campaign(); err != nil {
		t.Fatal(err)
	}
	c.stabilize()
	if c.nodes[1].rn.BasicStatus().RaftState != StateLeader {
		t.Fatal("node 1 is not leader")
	}

	// C1 = add 4 (index 2), committed; node 1 Advances without ApplyConfChange.
	if err := c.nodes[1].rn.ProposeConfChange(pb.ConfChange{Type: pb.ConfChangeAddNode, NodeId: 4}); err != nil {
		t.Fatal(err)
	}
	c.stabilize()

	// C2 = remove 2 (index 3). Accepted because pendingConfIndex (2) <= applied (2),
	// although node 1 has not applied C1 (it is still on C0 = {1,2,3}).
	if err := c.nodes[1].rn.ProposeConfChange(pb.ConfChange{Type: pb.ConfChangeRemoveNode, NodeId: 2}); err != nil {
		t.Fatal(err)
	}
	c.stabilize()
	if e := c.nodes[1].committed[3]; e.Type != pb.EntryConfChange {
		t.Fatalf("C2 was not accepted as a conf change at index 3: %+v", e)
	}
	if got := c.nodes[3].committed; len(got) != 3 {
		t.Fatalf("node 3 should have applied indices 1-3, has %d entries", len(got))
	}
	t.Logf("node 1 config %v (pending, unapplied conf changes: %d); node 3 config %v",
		c.cfg(1), len(c.nodes[1].pendingCC), c.cfg(3))

	// Phase 2: node 3 cut off. Node 1, still on C0, commits x at index 4 with {1,2}.
	c.drop = isolate(3, 4)
	if err := c.nodes[1].rn.Propose([]byte("x")); err != nil {
		t.Fatal(err)
	}
	c.stabilize()

	// Phase 3: {1,2} | {3,4}. Node 3 (config {1,3,4}) campaigns, wins with {3,4},
	// commits its empty entry (index 4) and y (index 5).
	c.drop = isolate(1, 2)
	if err := c.nodes[3].rn.Campaign(); err != nil {
		t.Fatal(err)
	}
	c.stabilize()
	if c.nodes[3].rn.BasicStatus().RaftState != StateLeader {
		t.Fatalf("node 3 did not win: state %v", c.nodes[3].rn.BasicStatus().RaftState)
	}
	if err := c.nodes[3].rn.Propose([]byte("y")); err != nil {
		t.Fatal(err)
	}
	c.stabilize()

	// Node 1's application eventually finishes applying (irrelevant to the result).
	for _, cc := range c.nodes[1].pendingCC {
		c.nodes[1].rn.ApplyConfChange(cc)
	}

	e1, ok1 := c.nodes[1].committed[4]
	e3, ok3 := c.nodes[3].committed[4]
	e4, ok4 := c.nodes[4].committed[4]
	t.Logf("index 4 committed on node 1: %v term=%d data=%q", ok1, e1.Term, e1.Data)
	t.Logf("index 4 committed on node 3: %v term=%d data=%q", ok3, e3.Term, e3.Data)
	t.Logf("index 4 committed on node 4: %v term=%d data=%q", ok4, e4.Term, e4.Data)
	t.Logf("index 5 committed on node 3: term=%d data=%q", c.nodes[3].committed[5].Term, c.nodes[3].committed[5].Data)
	// The violation: both committed, and different.
	if !ok1 || !ok3 || (e1.Term == e3.Term && bytes.Equal(e1.Data, e3.Data)) {
		t.Fatalf("safety violation NOT reproduced")
	}
	t.Logf("SAFETY VIOLATION reproduced: index 4 committed as %q (term %d) on node 1 and as %q (term %d) on node 3",
		e1.Data, e1.Term, e3.Data, e3.Term)
}
