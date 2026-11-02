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

// Reproduction: a cluster bootstrapped with an index-0 snapshot holding only the
// initial ConfState (which MemoryStorage.ApplySnapshot explicitly allows: "During
// bootstrap, applications (e.g., etcd) may initialize only the ConfState in the
// snapshot") and a node added later with empty storage. The leader's first index
// is 1, so it catches the new node up by MsgApp from index 1, never by snapshot:
// the new node applies the log's conf changes to its own empty configuration,
// not to the initial one. After "add 4" its configuration is {4}: it is
// promotable, wins an election alone and commits an entry at an index where the
// real cluster ({1,2,3,4}) committed another.
//
// Every application applies a Ready's conf changes before Advance (faithful);
// storage is synchronous MemoryStorage; messages are routed by hand; public
// RawNode API only (discardLogger aside). The test PASSES when the violation is
// reproduced.

import (
	"bytes"
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

type jnNode struct {
	id        uint64
	rn        *RawNode
	st        *MemoryStorage
	committed map[uint64]pb.Entry
}

type jnCluster struct {
	t     *testing.T
	nodes map[uint64]*jnNode
	queue []pb.Message
	drop  func(m pb.Message) bool
}

func newJNNode(t *testing.T, id uint64, voters []uint64) *jnNode {
	st := NewMemoryStorage()
	if len(voters) > 0 {
		if err := st.ApplySnapshot(pb.Snapshot{Metadata: pb.SnapshotMetadata{
			ConfState: pb.ConfState{Voters: voters},
		}}); err != nil {
			t.Fatal(err)
		}
	}
	rn, err := NewRawNode(&Config{
		ID: id, ElectionTick: 10, HeartbeatTick: 1, Storage: st,
		MaxSizePerMsg: noLimit, MaxInflightMsgs: 256, Logger: discardLogger,
	})
	if err != nil {
		t.Fatal(err)
	}
	return &jnNode{id: id, rn: rn, st: st, committed: map[uint64]pb.Entry{}}
}

func (c *jnCluster) handleReady(n *jnNode) {
	rd := n.rn.Ready()
	if !IsEmptyHardState(rd.HardState) {
		if err := n.st.SetHardState(rd.HardState); err != nil {
			c.t.Fatal(err)
		}
	}
	if !IsEmptySnap(rd.Snapshot) {
		if err := n.st.ApplySnapshot(rd.Snapshot); err != nil {
			c.t.Fatal(err)
		}
	}
	if err := n.st.Append(rd.Entries); err != nil {
		c.t.Fatal(err)
	}
	c.queue = append(c.queue, rd.Messages...)
	for _, e := range rd.CommittedEntries {
		n.committed[e.Index] = e
		if e.Type == pb.EntryConfChange {
			var cc pb.ConfChange
			if err := cc.Unmarshal(e.Data); err != nil {
				c.t.Fatal(err)
			}
			n.rn.ApplyConfChange(cc)
		}
	}
	n.rn.Advance(rd)
}

func (c *jnCluster) stabilize() {
	for i := 0; i < 10000; i++ {
		progress := false
		for id := uint64(1); id <= 4; id++ {
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

func TestJoinerWithoutBootstrapConfStateWinsAlone(t *testing.T) {
	c := &jnCluster{t: t, nodes: map[uint64]*jnNode{
		1: newJNNode(t, 1, []uint64{1, 2, 3}),
		2: newJNNode(t, 2, []uint64{1, 2, 3}),
		3: newJNNode(t, 3, []uint64{1, 2, 3}),
		4: newJNNode(t, 4, nil), // added later: empty storage
	}}
	c.drop = func(pb.Message) bool { return false }
	n1, n4 := c.nodes[1], c.nodes[4]
	if err := n1.rn.Campaign(); err != nil {
		t.Fatal(err)
	}
	c.stabilize()
	if err := n1.rn.ProposeConfChange(pb.ConfChange{Type: pb.ConfChangeAddNode, NodeId: 4}); err != nil {
		t.Fatal(err)
	}
	c.stabilize()
	if _, ok := n4.committed[2]; !ok {
		t.Fatal("node 4 did not catch up")
	}
	t.Logf("node 1 config %v; node 4 config %v (caught up by MsgApp from index 1)",
		n1.rn.Status().Config, n4.rn.Status().Config)

	// Node 4 cut off. The cluster commits x at index 3 with {1,2,3}.
	c.drop = func(m pb.Message) bool { return m.From != m.To && (m.From == 4 || m.To == 4) }
	if err := n1.rn.Propose([]byte("x")); err != nil {
		t.Fatal(err)
	}
	c.stabilize()
	// Node 4 campaigns: it is a voter of its configuration {4} and has no
	// unapplied conf change, so it wins on its own vote.
	if err := n4.rn.Campaign(); err != nil {
		t.Fatal(err)
	}
	c.stabilize()
	if n4.rn.BasicStatus().RaftState != StateLeader {
		t.Fatalf("node 4 did not win: %v", n4.rn.BasicStatus().RaftState)
	}
	a, b := n1.committed[3], n4.committed[3]
	if a.Index == 3 && b.Index == 3 && (a.Term != b.Term || !bytes.Equal(a.Data, b.Data)) {
		t.Logf("SAFETY VIOLATION reproduced: index 3 committed as %q (term %d) on node 1 and as %q (term %d) on node 4",
			a.Data, a.Term, b.Data, b.Term)
	} else {
		t.Fatalf("no conflicting commit: node 1 %+v, node 4 %+v", a, b)
	}
}
