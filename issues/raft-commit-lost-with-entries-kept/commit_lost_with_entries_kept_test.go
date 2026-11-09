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

import (
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"google.golang.org/protobuf/proto"

	pb "go.etcd.io/raft/v3/raftpb"
)

// TestRestartWithEntriesButNotCommit runs five RawNodes with etcd's settings
// (PreVote, CheckQuorum), each application handling a Ready as doc.go
// describes: persist HardState and Entries, send Messages, apply
// CommittedEntries (conf changes included), then Advance. Node 1 crashes while
// handling a Ready after its Entries are durable but before its HardState is,
// as a crash in the middle of step 1 can leave it, and restarts from its
// storage. No index may then be committed with two different entries.
func TestRestartWithEntriesButNotCommit(t *testing.T) {
	type member struct {
		rn        *RawNode
		s         *MemoryStorage
		committed map[uint64]*pb.Entry
	}
	cfg := func(id uint64, s *MemoryStorage) *Config {
		c := newTestConfig(id, 10, 1, s)
		c.PreVote = true
		c.CheckQuorum = true
		return c
	}
	ms := map[uint64]*member{}
	for id := uint64(1); id <= 5; id++ {
		// Voters 1, 2, 3; nodes 4 and 5 are started to be added later.
		s := newTestMemoryStorage(withPeers(1, 2, 3))
		rn, err := NewRawNode(cfg(id, s))
		require.NoError(t, err)
		ms[id] = &member{rn: rn, s: s, committed: map[uint64]*pb.Entry{}}
	}

	side := map[uint64]int{} // nodes talk only to nodes on the same side
	crash := false           // node 1 crashes in the middle of its next Ready with entries
	var crashed Ready
	stabilize := func() {
		for busy := true; busy; {
			busy = false
			var msgs []*pb.Message
			for id := uint64(1); id <= 5; id++ {
				m := ms[id]
				if !m.rn.HasReady() {
					continue
				}
				busy = true
				rd := m.rn.Ready()
				if id == 1 && crash && len(rd.Entries) > 0 {
					// Step 1 of doc.go, interrupted: the entries are on
					// disk, the HardState is not. Nothing else happens
					// before the crash; node 1 restarts from its storage.
					require.NoError(t, m.s.Append(rd.Entries))
					crash, crashed = false, rd
					rn, err := NewRawNode(cfg(1, m.s))
					require.NoError(t, err)
					m.rn = rn
					continue
				}
				if !IsEmptyHardState(rd.HardState) {
					require.NoError(t, m.s.SetHardState(rd.HardState))
				}
				require.NoError(t, m.s.Append(rd.Entries))
				msgs = append(msgs, rd.Messages...)
				for _, e := range rd.CommittedEntries {
					m.committed[e.GetIndex()] = e
					if e.GetType() == pb.EntryConfChange {
						cc := &pb.ConfChange{}
						require.NoError(t, proto.Unmarshal(e.GetData(), cc))
						m.rn.ApplyConfChange(cc)
					}
				}
				m.rn.Advance(rd)
			}
			for _, msg := range msgs {
				if side[msg.GetFrom()] == side[msg.GetTo()] {
					_ = ms[msg.GetTo()].rn.Step(msg)
				}
			}
		}
	}

	// Node 3 leads term 1 with voters 1, 2, 3; index 1 is committed everywhere.
	require.NoError(t, ms[3].rn.Campaign())
	stabilize()
	require.Equal(t, StateLeader, ms[3].rn.raft.state)
	require.Equal(t, uint64(1), ms[1].rn.raft.raftLog.committed)

	// With node 1 cut off, node 3 adds voter 4 (index 2), then voter 5
	// (index 3), each committed and applied by nodes 2 to 5.
	side[1] = 1
	for _, id := range []uint64{4, 5} {
		cc := &pb.ConfChange{Type: pb.ConfChangeAddNode.Enum(), NodeId: new(id)}
		require.NoError(t, ms[3].rn.ProposeConfChange(cc))
		stabilize()
	}
	for id := uint64(2); id <= 5; id++ {
		require.Equal(t, uint64(3), ms[id].rn.raft.raftLog.committed, "node %d", id)
		require.Len(t, ms[id].rn.raft.trk.Voters.IDs(), 5, "node %d", id)
	}

	// Node 1 is reconnected and receives indexes 2 and 3 with commit index 3
	// in one Ready; it crashes after persisting the entries only.
	side[1] = 0
	crash = true
	ms[3].rn.Tick() // heartbeat
	stabilize()
	require.False(t, crash, "node 1 did not crash")
	require.Equal(t, uint64(3), crashed.Entries[len(crashed.Entries)-1].GetIndex())
	require.Equal(t, uint64(3), crashed.HardState.GetCommit(), "the crashed Ready carried commit 3")
	require.Equal(t, uint64(1), ms[1].rn.raft.raftLog.committed, "restarted with commit 1")
	require.Equal(t, uint64(3), ms[1].rn.raft.raftLog.lastIndex())

	// Partition {1, 2} | {3, 4, 5}. Node 3 commits y at index 4 with 4 and 5.
	side[1], side[2] = 1, 1
	require.NoError(t, ms[3].rn.Propose([]byte("y")))
	stabilize()
	require.Contains(t, ms[3].committed, uint64(4))

	// Node 2's election timeout elapses (it cannot win: it counts in
	// {1,...,5}). Node 1 campaigns in {1, 2, 3} and wins with node 2's vote.
	for i := 0; i < 20; i++ {
		ms[2].rn.Tick()
		stabilize()
	}
	require.NoError(t, ms[1].rn.Campaign())
	stabilize()
	require.Equal(t, StateLeader, ms[1].rn.raft.state)
	require.Equal(t, StateLeader, ms[3].rn.raft.state)

	require.Contains(t, ms[1].committed, uint64(4))
	assert.Equal(t, DescribeEntry(ms[3].committed[4], nil), DescribeEntry(ms[1].committed[4], nil),
		"index 4 committed on nodes 3 and 1")
}
