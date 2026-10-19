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

// What a gap of two terms adds to issues/etcd-merged-snapshot-stale-term.md (copy into a
// raft checkout, `go test -run TestStaleSnapGap2 .`).
//
// Node 5 (E) is at term 1 and installs a merged MsgSnap stamped term 1 whose snapshot is
// (index 3, term 3): the state merged_snapshot_stale_term_test.go reaches with a gap of
// one, here with content two terms newer. E is then at term 1 with commit 3. A leader of
// the term in between, node 1 (L) at term 2, still up (cut off from the term-3 quorum),
// probes E. E steps up to term 2 and, since the probe's index is below its commit,
// answers MsgAppResp{Index: 3}: an acceptance at term 2 of a log L never had. L's
// Progress[5].Match becomes 3, past L's last index.
//
// The messages are built by hand; reaching E's state is the gap-of-one reproduction
// with one more election inside the stall (term 3's leader elected after term 2's).

import (
	"testing"

	"github.com/stretchr/testify/require"

	pb "go.etcd.io/raft/v3/raftpb"
)

func staleE(t *testing.T) *raft {
	e := newTestRaft(5, 10, 1, newTestMemoryStorage(withPeers(1, 2, 3, 4, 5)))
	e.becomeFollower(1, None)
	snap := &pb.Snapshot{Metadata: &pb.SnapshotMetadata{Index: new(uint64(3)), Term: new(uint64(3)),
		ConfState: &pb.ConfState{Voters: []uint64{1, 2, 3, 4, 5}}}}
	require.NoError(t, e.Step(&pb.Message{Type: pb.MsgSnap.Enum(), From: new(uint64(3)), To: new(uint64(5)),
		Term: new(uint64(1)), Snapshot: snap}))
	require.Equal(t, uint64(1), e.Term)
	require.Equal(t, uint64(3), e.raftLog.lastIndex())
	lt, err := e.raftLog.term(3)
	require.NoError(t, err)
	require.Equal(t, uint64(3), lt) // last log term 3 at term 1
	e.readMessages()
	return e
}

func leaderAt2(t *testing.T) *raft {
	l := newTestRaft(1, 10, 1, newTestMemoryStorage(withPeers(1, 2, 3, 4, 5)))
	l.becomeCandidate()
	l.becomeCandidate()
	require.Equal(t, uint64(2), l.Term)
	l.becomeLeader() // appends the empty entry (index 1, term 2)
	require.Equal(t, uint64(1), l.raftLog.lastIndex())
	l.readMessages()
	return l
}

// deliver steps m into r and returns r's outgoing messages to `to`.
func deliver(t *testing.T, r *raft, m *pb.Message, to uint64) []*pb.Message {
	require.NoError(t, r.Step(m))
	var out []*pb.Message
	for _, x := range r.readMessages() {
		if x.GetTo() == to {
			out = append(out, x)
		}
	}
	return out
}

func probe(t *testing.T, l *raft) *pb.Message {
	l.sendAppend(5)
	for _, m := range l.readMessages() {
		if m.GetTo() == 5 && m.GetType() == pb.MsgApp {
			return m
		}
	}
	t.Fatal("no MsgApp to 5")
	return nil
}

func TestStaleSnapGap2AckPastLeaderLog(t *testing.T) {
	e, l := staleE(t), leaderAt2(t)
	app := probe(t, l)
	require.Equal(t, uint64(2), app.GetTerm())
	require.Less(t, app.GetIndex(), uint64(3))

	resp := deliver(t, e, app, 1)
	require.Len(t, resp, 1)
	require.Equal(t, uint64(2), e.Term)
	require.Equal(t, pb.MsgAppResp, resp[0].GetType())
	require.False(t, resp[0].GetReject())
	require.Equal(t, uint64(3), resp[0].GetIndex()) // E "accepts" up to 3 at term 2
	t.Logf("E at term %d answers L: %v", e.Term, resp[0])

	// L takes it as an acknowledgement past its own log. Stepping it also makes L send
	// to E again (Match moved), from Next-1 = 3 > lastIndex = 1: term(3) is unavailable,
	// so maybeSendAppend falls back to maybeSendSnapshot. L's storage has no snapshot (a
	// fresh member), and that panics.
	defer func() {
		r := recover()
		pr := l.trk.Progress[5]
		t.Logf("L: lastIndex %d, Progress[5] %v, recovered %v", l.raftLog.lastIndex(), pr, r)
		require.Equal(t, uint64(3), pr.Match)
		require.Greater(t, pr.Match, l.raftLog.lastIndex())
	}()
	require.NoError(t, l.Step(resp[0]))
	t.Logf("L stepped the response; messages: %v", l.readMessages())
}
