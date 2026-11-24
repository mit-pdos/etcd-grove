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

// TestRestartWithPartOfBootstrapEntries runs three RawNodes bootstrapped as
// StartNode bootstraps them (voters 1, 2, 3; one conf change entry each, at
// indexes 1 to 3, committed at once), with MaxSizePerMsg 1 (one entry per
// append), PreVote and CheckQuorum, each Ready handled as doc.go describes.
// Nodes 1 and 2 crash while persisting their first Ready: the first entry is
// on disk, the HardState is not, and they restart from their storage. No index
// may then be committed with two different entries.
func TestRestartWithPartOfBootstrapEntries(t *testing.T) {
	type member struct {
		rn        *RawNode
		s         *MemoryStorage
		committed map[uint64]*pb.Entry
	}
	cfg := func(id uint64, s *MemoryStorage) *Config {
		c := newTestConfig(id, 10, 1, s)
		c.MaxSizePerMsg = 1
		c.PreVote = true
		c.CheckQuorum = true
		return c
	}
	peers := []Peer{{ID: 1}, {ID: 2}, {ID: 3}}
	ms := map[uint64]*member{}
	for id := uint64(1); id <= 3; id++ {
		s := NewMemoryStorage()
		rn, err := NewRawNode(cfg(id, s))
		require.NoError(t, err)
		require.NoError(t, rn.Bootstrap(peers))
		ms[id] = &member{rn: rn, s: s, committed: map[uint64]*pb.Entry{}}
	}

	var net []*pb.Message
	side := map[uint64]int{} // nodes talk only to nodes on the same side
	handle := func(id uint64) {
		m := ms[id]
		if !m.rn.HasReady() {
			return
		}
		rd := m.rn.Ready()
		if !IsEmptyHardState(rd.HardState) {
			require.NoError(t, m.s.SetHardState(rd.HardState))
		}
		require.NoError(t, m.s.Append(rd.Entries))
		net = append(net, rd.Messages...)
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
	// deliver handles Readies and delivers messages until none is left or
	// stop holds.
	deliver := func(stop func() bool) {
		for busy := true; busy && !stop(); {
			busy = false
			for id := uint64(1); id <= 3; id++ {
				if ms[id].rn.HasReady() {
					busy = true
					handle(id)
				}
			}
			if len(net) > 0 && !stop() {
				busy = true
				msg := net[0]
				net = net[1:]
				if side[msg.GetFrom()] == side[msg.GetTo()] {
					_ = ms[msg.GetTo()].rn.Step(msg)
				}
			}
		}
	}

	// Node 3 persists its first Ready. Nodes 1 and 2 crash in the middle of
	// theirs: index 1 is on disk, the HardState (commit 3) is not.
	for ms[3].rn.HasReady() {
		handle(3)
	}
	for _, id := range []uint64{1, 2} {
		m := ms[id]
		rd := m.rn.Ready()
		require.Len(t, rd.Entries, 3)
		require.Equal(t, uint64(3), rd.HardState.GetCommit())
		require.NoError(t, m.s.Append(rd.Entries[:1]))
		rn, err := NewRawNode(cfg(id, m.s))
		require.NoError(t, err)
		m.rn = rn
	}

	// Node 2 is cut off. Node 3 wins an election with node 1's vote and
	// replicates its log to node 1, one entry per append; node 1 learns that
	// index 2 is committed, applies the first two conf changes (voters 1, 2)
	// and is then cut off from node 3.
	side[2] = 1
	require.NoError(t, ms[3].rn.Campaign())
	deliver(func() bool { return ms[1].rn.raft.raftLog.committed >= 2 })
	require.Equal(t, StateLeader, ms[3].rn.raft.state)
	require.Equal(t, uint64(2), ms[1].rn.raft.raftLog.committed)
	deliver(func() bool { return !ms[1].rn.HasReady() })
	net = nil
	require.Contains(t, ms[3].committed, uint64(3))

	// Partition {1, 2} | {3}. Node 1 campaigns in {1, 2} and wins with node
	// 2's vote, then commits its empty entry at index 3 with node 2.
	side[1], side[2], side[3] = 1, 1, 0
	require.NoError(t, ms[1].rn.Campaign())
	deliver(func() bool { return false })
	require.Equal(t, StateLeader, ms[1].rn.raft.state)

	require.Contains(t, ms[1].committed, uint64(3))
	assert.Equal(t, DescribeEntry(ms[3].committed[3], nil), DescribeEntry(ms[1].committed[3], nil),
		"index 3 committed on nodes 3 and 1")
}
