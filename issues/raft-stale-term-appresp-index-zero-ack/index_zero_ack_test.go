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

	"github.com/stretchr/testify/require"

	pb "go.etcd.io/raft/v3/raftpb"
	"go.etcd.io/raft/v3/tracker"
)

// TestStaleMsgAppGetsIndexZeroAck: a follower at term 2 answers a stale MsgApp
// of term 1 (check-quorum on) with an empty MsgAppResp of its own term: Index
// 0, not a rejection. (Passes: it shows the message the next test receives.)
func TestStaleMsgAppGetsIndexZeroAck(t *testing.T) {
	s := newTestMemoryStorage(withPeers(1, 2, 3))
	require.NoError(t, s.Append(index(1).terms(1, 1, 1)))
	r := newTestRaft(2, 10, 1, s)
	r.checkQuorum = true
	r.becomeFollower(2, None) // voted in term 2, no leader heard yet
	require.NoError(t, r.Step(&pb.Message{From: new(uint64(1)), To: new(uint64(2)), Term: new(uint64(1)),
		Type: pb.MsgApp.Enum(), Index: new(uint64(3)), LogTerm: new(uint64(1))}))
	msgs := r.readMessages()
	if len(msgs) != 1 || msgs[0].GetType() != pb.MsgAppResp || msgs[0].GetTo() != 1 ||
		msgs[0].GetTerm() != 2 || msgs[0].GetIndex() != 0 || msgs[0].GetReject() {
		t.Fatalf("unexpected response %v", msgs)
	}
}

// TestLeaderIndexZeroAckSendsNoSnapshot: a leader of term 2 that has not yet
// heard from peer 2 (StateProbe, Match 0, Next 4) receives the response of
// TestStaleMsgAppGetsIndexZeroAck. It acknowledges nothing: the leader must not
// move 2 to StateReplicate with Next = 1, which, with its log compacted at
// index 1, would send 2 a MsgSnap although 2 holds the whole log.
func TestLeaderIndexZeroAckSendsNoSnapshot(t *testing.T) {
	s := newTestMemoryStorage(withPeers(1, 2, 3))
	require.NoError(t, s.Append(index(1).terms(1, 1, 1)))
	require.NoError(t, s.SetHardState(&pb.HardState{Term: new(uint64(1)), Commit: new(uint64(3))}))
	cs := &pb.ConfState{Voters: []uint64{1, 2, 3}}
	_, err := s.CreateSnapshot(3, cs, nil)
	require.NoError(t, err)
	require.NoError(t, s.Compact(1))
	r := newTestRaft(1, 10, 1, s)
	r.checkQuorum = true
	r.becomeCandidate() // term 2
	r.becomeLeader()
	r.readMessages()
	pr := r.trk.Progress[2]
	require.Equal(t, tracker.StateProbe, pr.State)
	require.Equal(t, uint64(0), pr.Match)
	require.Equal(t, uint64(4), pr.Next)
	require.NoError(t, r.Step(&pb.Message{From: new(uint64(2)), To: new(uint64(1)), Term: new(uint64(2)),
		Type: pb.MsgAppResp.Enum()}))
	for _, m := range r.readMessages() {
		require.NotEqual(t, pb.MsgSnap, m.GetType(), "%v", DescribeMessage(m, nil))
	}
	pr = r.trk.Progress[2]
	require.Equal(t, tracker.StateProbe, pr.State, "%v", pr)
}
