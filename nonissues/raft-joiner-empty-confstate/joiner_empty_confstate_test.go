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

// A cluster bootstrapped with an index-0 snapshot holding only the initial
// ConfState (which MemoryStorage.ApplySnapshot's comment allows: "During
// bootstrap, applications (e.g., etcd) may initialize only the ConfState in the
// snapshot") and a node added later with empty storage. The leader's first index
// is 1, so it catches the new node up by MsgApp from index 1, never by snapshot:
// the new node applies the log's conf changes to its own empty configuration.
// After "add 4" its configuration is {4}: it wins an election alone and commits
// an entry at an index where the cluster committed another.
//
// Conf changes are applied before Advance; storage is a synchronous
// MemoryStorage; messages are routed by hand; public RawNode API only.

import (
	"bytes"
	"testing"

	"github.com/stretchr/testify/require"
	"google.golang.org/protobuf/proto"

	pb "go.etcd.io/raft/v3/raftpb"
)

type jnNode struct {
	id        uint64
	rn        *RawNode
	st        *MemoryStorage
	committed map[uint64]*pb.Entry
}

type jnCluster struct {
	t     *testing.T
	nodes map[uint64]*jnNode
	queue []*pb.Message
	drop  func(m *pb.Message) bool
}

func newJNNode(t *testing.T, id uint64, voters []uint64) *jnNode {
	st := NewMemoryStorage()
	if len(voters) > 0 {
		require.NoError(t, st.ApplySnapshot(&pb.Snapshot{Metadata: &pb.SnapshotMetadata{
			ConfState: &pb.ConfState{Voters: voters},
		}}))
	}
	rn, err := NewRawNode(&Config{
		ID: id, ElectionTick: 10, HeartbeatTick: 1, Storage: st,
		MaxSizePerMsg: noLimit, MaxInflightMsgs: 256, Logger: discardLogger,
	})
	require.NoError(t, err)
	return &jnNode{id: id, rn: rn, st: st, committed: map[uint64]*pb.Entry{}}
}

func (c *jnCluster) handleReady(n *jnNode) {
	rd := n.rn.Ready()
	if !IsEmptyHardState(rd.HardState) {
		require.NoError(c.t, n.st.SetHardState(rd.HardState))
	}
	if !IsEmptySnap(rd.Snapshot) {
		require.NoError(c.t, n.st.ApplySnapshot(rd.Snapshot))
	}
	require.NoError(c.t, n.st.Append(rd.Entries))
	c.queue = append(c.queue, rd.Messages...)
	for _, e := range rd.CommittedEntries {
		n.committed[e.GetIndex()] = e
		if e.GetType() == pb.EntryConfChange {
			cc := &pb.ConfChange{}
			require.NoError(c.t, proto.Unmarshal(e.GetData(), cc))
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
			_ = c.nodes[m.GetTo()].rn.Step(m)
		}
		if !progress {
			return
		}
	}
	c.t.Fatal("did not stabilize")
}

func TestJoinerWithoutBootstrapConfState(t *testing.T) {
	c := &jnCluster{t: t, nodes: map[uint64]*jnNode{
		1: newJNNode(t, 1, []uint64{1, 2, 3}),
		2: newJNNode(t, 2, []uint64{1, 2, 3}),
		3: newJNNode(t, 3, []uint64{1, 2, 3}),
		4: newJNNode(t, 4, nil), // added later: empty storage
	}}
	c.drop = func(*pb.Message) bool { return false }
	n1, n4 := c.nodes[1], c.nodes[4]
	require.NoError(t, n1.rn.Campaign())
	c.stabilize()
	require.NoError(t, n1.rn.ProposeConfChange(&pb.ConfChange{Type: pb.ConfChangeAddNode.Enum(), NodeId: new(uint64(4))}))
	c.stabilize()
	require.Contains(t, n4.committed, uint64(2), "node 4 did not catch up")
	t.Logf("node 1 config %v; node 4 config %v", n1.rn.Status().Config, n4.rn.Status().Config)

	// Node 4 is cut off. The cluster commits x at index 3 with {1,2,3}.
	c.drop = func(m *pb.Message) bool {
		return m.GetFrom() != m.GetTo() && (m.GetFrom() == 4 || m.GetTo() == 4)
	}
	require.NoError(t, n1.rn.Propose([]byte("x")))
	c.stabilize()
	require.Contains(t, n1.committed, uint64(3))

	// Node 4 campaigns while cut off.
	require.NoError(t, n4.rn.Campaign())
	c.stabilize()

	// No two nodes may commit different entries at the same index.
	if b, ok := n4.committed[3]; ok {
		a := n1.committed[3]
		if a.GetTerm() != b.GetTerm() || !bytes.Equal(a.GetData(), b.GetData()) {
			t.Fatalf("index 3 committed as %q (term %d) on node 1 and as %q (term %d) on node 4",
				a.GetData(), a.GetTerm(), b.GetData(), b.GetTerm())
		}
	}
}
