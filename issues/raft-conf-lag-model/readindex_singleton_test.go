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

// Reproductions: ReadOnlySafe read index is not linearizable once a
// configuration change leaves a single voter. stepLeader's MsgReadIndex fast
// path (raft.go, `if r.trk.IsSingleton()`) answers with the leader's commit
// index at once: it neither waits for an entry of the leader's term to commit
// (committedEntryInCurrentTerm, which the multi-voter path checks) nor checks
// that the single voter is the leader itself.
//
//   - TestReadIndexSingletonNewLeaderStale: C0 = {1,2}, node 2 leads term 1 and
//     removes itself (C1 = {1}). Node 1 learns that C1 is committed but not that
//     the next entry x is. Node 1 wins term 2 alone; before its first Advance as
//     leader, a ReadIndex returns its commit index 2, while x (index 3) was
//     committed and applied by node 2 before the read was issued.
//   - TestReadIndexSingletonRemovedLeaderStale: the same start; node 2 stays
//     leader after its removal (StepDownOnRemoval is false, the default), with
//     configuration {1}: IsSingleton holds although node 2 is not a voter.
//     Partitioned from node 1, which wins term 2 and commits y, node 2 keeps
//     answering read index requests from its own commit index.
//
// Every application here applies a Ready's conf changes before Advance (the
// precondition of raft-advance-before-applyconfchange.md); storage is
// synchronous MemoryStorage; messages are routed by hand. Public RawNode API
// only, except that the cluster is built with the package-internal
// discardLogger. The tests PASS when the violation is reproduced.

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

type riNode struct {
	id        uint64
	rn        *RawNode
	st        *MemoryStorage
	committed map[uint64]pb.Entry // what the application applied
	reads     []ReadState
}

type riCluster struct {
	t     *testing.T
	nodes map[uint64]*riNode
	queue []pb.Message
	drop  func(m pb.Message) bool
}

func newRINode(t *testing.T, id uint64, voters []uint64) *riNode {
	st := NewMemoryStorage()
	if err := st.ApplySnapshot(pb.Snapshot{Metadata: pb.SnapshotMetadata{
		ConfState: pb.ConfState{Voters: voters},
	}}); err != nil {
		t.Fatal(err)
	}
	rn, err := NewRawNode(&Config{
		ID:              id,
		ElectionTick:    10,
		HeartbeatTick:   1,
		Storage:         st,
		MaxSizePerMsg:   noLimit,
		MaxInflightMsgs: 256,
		Logger:          discardLogger,
		ReadOnlyOption:  ReadOnlySafe,
	})
	if err != nil {
		t.Fatal(err)
	}
	return &riNode{id: id, rn: rn, st: st, committed: map[uint64]pb.Entry{}}
}

// handleReady: persist, send, apply (ApplyConfChange first), then Advance.
func (c *riCluster) handleReady(n *riNode) {
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
	n.reads = append(n.reads, rd.ReadStates...)
	for _, e := range rd.CommittedEntries {
		n.committed[e.Index] = e
		switch e.Type {
		case pb.EntryConfChange:
			var cc pb.ConfChange
			if err := cc.Unmarshal(e.Data); err != nil {
				c.t.Fatal(err)
			}
			n.rn.ApplyConfChange(cc)
		case pb.EntryConfChangeV2:
			var cc pb.ConfChangeV2
			if err := cc.Unmarshal(e.Data); err != nil {
				c.t.Fatal(err)
			}
			n.rn.ApplyConfChange(cc)
		}
	}
	n.rn.Advance(rd)
}

func (c *riCluster) stabilize() {
	for i := 0; i < 10000; i++ {
		progress := false
		for id := uint64(1); id <= 2; id++ {
			if n := c.nodes[id]; n.rn.HasReady() {
				c.handleReady(n)
				progress = true
			}
		}
		msgs := c.queue
		c.queue = nil
		for _, m := range msgs {
			if c.drop(m) {
				continue
			}
			progress = true
			_ = c.nodes[m.To].rn.Step(m)
		}
		if !progress {
			return
		}
	}
	c.t.Fatal("did not stabilize")
}

// setup: node 2 leads term 1 of C0 = {1,2}, removes itself (index 2) and
// commits x (index 3); node 1 learns that index 2 is committed, not index 3.
func riSetup(t *testing.T) *riCluster {
	c := &riCluster{t: t, nodes: map[uint64]*riNode{
		1: newRINode(t, 1, []uint64{1, 2}),
		2: newRINode(t, 2, []uint64{1, 2}),
	}}
	c.drop = func(pb.Message) bool { return false }
	n1, n2 := c.nodes[1], c.nodes[2]
	if err := n2.rn.Campaign(); err != nil {
		t.Fatal(err)
	}
	c.stabilize()
	if n2.rn.BasicStatus().RaftState != StateLeader {
		t.Fatal("node 2 is not leader")
	}
	// The removal (index 2), sent on its own; then x (index 3), proposed before
	// node 2 applies its removal (afterwards it would drop proposals).
	if err := n2.rn.ProposeConfChange(pb.ConfChange{Type: pb.ConfChangeRemoveNode, NodeId: 2}); err != nil {
		t.Fatal(err)
	}
	c.handleReady(n2)
	if err := n2.rn.Propose([]byte("x")); err != nil {
		t.Fatal(err)
	}
	// From now on node 1 never hears that index 3 is committed (lost messages).
	c.drop = func(m pb.Message) bool {
		return m.From == 2 && m.To == 1 && m.Commit >= 3
	}
	c.stabilize()
	if e, ok := n2.committed[3]; !ok || string(e.Data) != "x" {
		t.Fatalf("node 2 did not commit and apply x at index 3: %+v", n2.committed)
	}
	if st := n1.rn.BasicStatus(); st.Commit != 2 || st.Applied != 2 {
		t.Fatalf("node 1: commit %d applied %d, want 2 and 2", st.Commit, st.Applied)
	}
	t.Logf("node 1 config %v; node 2 config %v, state %v; x committed and applied at index 3 on node 2",
		n1.rn.Status().Config, n2.rn.Status().Config, n2.rn.BasicStatus().RaftState)
	return c
}

func TestReadIndexSingletonNewLeaderStale(t *testing.T) {
	c := riSetup(t)
	n1 := c.nodes[1]
	// Node 1 (configuration {1}) campaigns and wins term 2 on its own vote.
	if err := n1.rn.Campaign(); err != nil {
		t.Fatal(err)
	}
	c.handleReady(n1) // persists the vote; Advance steps it: becomeLeader
	if n1.rn.BasicStatus().RaftState != StateLeader {
		t.Fatalf("node 1 did not win: %v", n1.rn.BasicStatus().RaftState)
	}
	// A read issued now, after x was committed and applied by node 2.
	n1.rn.ReadIndex([]byte("r"))
	c.stabilize()
	if len(n1.reads) != 1 {
		t.Fatalf("no read state: %+v", n1.reads)
	}
	if got := n1.reads[0].Index; got < 3 {
		t.Logf("STALE READ reproduced: read index %d at node 1 (term 2), but x was committed at index 3 before the read", got)
	} else {
		t.Fatalf("read index %d covers x", got)
	}
	if e := n1.committed[3]; string(e.Data) != "x" {
		t.Fatalf("node 1 later committed %+v at index 3", e)
	}
}

func TestReadIndexSingletonRemovedLeaderStale(t *testing.T) {
	c := riSetup(t)
	n1, n2 := c.nodes[1], c.nodes[2]
	if n2.rn.BasicStatus().RaftState != StateLeader {
		t.Fatal("node 2 stepped down")
	}
	// Partition {1} | {2}. Node 1 wins term 2 alone and commits y.
	c.drop = func(m pb.Message) bool { return m.From != m.To }
	if err := n1.rn.Campaign(); err != nil {
		t.Fatal(err)
	}
	c.stabilize()
	if err := n1.rn.Propose([]byte("y")); err != nil {
		t.Fatal(err)
	}
	c.stabilize()
	yIdx := uint64(0)
	for i, e := range n1.committed {
		if string(e.Data) == "y" {
			yIdx = i
		}
	}
	if yIdx == 0 {
		t.Fatal("node 1 did not commit y")
	}
	// A read at node 2, still leader of term 1 with configuration {1}.
	n2.rn.ReadIndex([]byte("r"))
	c.stabilize()
	if len(n2.reads) != 1 {
		t.Fatalf("node 2 gave no read state: %+v", n2.reads)
	}
	if got := n2.reads[0].Index; got < yIdx {
		t.Logf("STALE READ reproduced: removed leader 2 answered read index %d; y was committed at index %d (term 2) before the read", got, yIdx)
	} else {
		t.Fatalf("read index %d covers y", got)
	}
}
