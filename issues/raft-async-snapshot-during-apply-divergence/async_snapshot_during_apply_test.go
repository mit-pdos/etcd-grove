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

// With AsyncStorageWrites, raft hands out a snapshot (in a MsgStorageAppend, to
// the append thread) while committed entries it handed out earlier (in a
// MsgStorageApply, to the apply thread) are still being applied. Config's
// documentation says MsgStorageAppend carries "snapshots to apply" to "local
// storage (raft log and state machine)", and that "messages to different
// targets can be processed in any order". An application that follows it,
// with the append thread installing the snapshot before the apply thread
// finishes the older entries, applies those entries on top of the snapshot,
// which already includes them: the state machine is no longer that of any
// prefix of the log, while raft's applied index is the snapshot's.
//
// The state machine appends each entry's data (as rafttest's does). Follower 2
// gets entry 1 ("a") committed; the leader then sends a snapshot at index 2
// whose state is "ab".
//
// The test PASSES when the divergence is reproduced.

import (
	"testing"

	"github.com/stretchr/testify/require"

	pb "go.etcd.io/raft/v3/raftpb"
)

func TestAsyncSnapshotDuringApplyDivergence(t *testing.T) {
	s := newTestMemoryStorage(withPeers(1, 2, 3))
	cfg := newTestConfig(2, 10, 1, s)
	cfg.AsyncStorageWrites = true
	rn, err := NewRawNode(cfg)
	require.NoError(t, err)

	var sm []byte // the application's state machine
	var appendWork, applyWork []*pb.Message
	// ready queues the Ready's local storage messages for their threads.
	ready := func() {
		rd := rn.Ready()
		for _, m := range rd.Messages {
			switch m.GetTo() {
			case LocalAppendThread:
				appendWork = append(appendWork, m)
			case LocalApplyThread:
				applyWork = append(applyWork, m)
			}
		}
	}
	// respond delivers a storage message's responses addressed to node 2.
	respond := func(m *pb.Message) {
		for _, r := range m.GetResponses() {
			if r.GetTo() == 2 {
				require.NoError(t, rn.Step(r))
			}
		}
	}
	// The append thread: persist, and apply a snapshot to storage and the
	// state machine.
	processAppend := func() {
		m := appendWork[0]
		appendWork = appendWork[1:]
		if m.Vote != nil || m.Commit != nil {
			require.NoError(t, s.SetHardState(&pb.HardState{Term: new(m.GetTerm()), Vote: new(m.GetVote()), Commit: new(m.GetCommit())}))
		}
		if snap := m.GetSnapshot(); snap != nil {
			require.NoError(t, s.ApplySnapshot(snap))
			sm = append([]byte(nil), snap.GetData()...)
		} else {
			require.NoError(t, s.Append(m.GetEntries()))
		}
		respond(m)
	}
	// The apply thread: apply committed entries to the state machine.
	processApply := func() {
		m := applyWork[0]
		applyWork = applyWork[1:]
		for _, e := range m.GetEntries() {
			sm = append(sm, e.GetData()...)
		}
		respond(m)
	}

	// Leader 1 replicates entry 1 ("a") and commits it.
	require.NoError(t, rn.Step(&pb.Message{From: new(uint64(1)), To: new(uint64(2)), Term: new(uint64(1)),
		Type: pb.MsgApp.Enum(), Index: new(uint64(0)), LogTerm: new(uint64(0)), Commit: new(uint64(1)),
		Entries: []*pb.Entry{{Term: new(uint64(1)), Index: new(uint64(1)), Data: []byte("a")}}}))
	ready()
	processAppend() // entry 1 is stable
	ready()
	require.Len(t, applyWork, 1, "entry 1 handed out to the apply thread")

	// While the apply thread applies entry 1, the leader's snapshot at index 2
	// (state "ab") arrives, and raft hands it out to the append thread.
	require.NoError(t, rn.Step(&pb.Message{From: new(uint64(1)), To: new(uint64(2)), Term: new(uint64(1)),
		Type: pb.MsgSnap.Enum(), Snapshot: &pb.Snapshot{Data: []byte("ab"), Metadata: &pb.SnapshotMetadata{
			Index: new(uint64(2)), Term: new(uint64(1)), ConfState: &pb.ConfState{Voters: []uint64{1, 2, 3}}}}}))
	ready()
	require.Len(t, appendWork, 1)
	require.NotNil(t, appendWork[0].GetSnapshot(), "snapshot handed out while entry 1 is being applied")
	t.Logf("raft handed out the snapshot with applying=%d > applied=%d", rn.raft.raftLog.applying, rn.raft.raftLog.applied)

	// The append thread gets to its message first: it installs the snapshot.
	// Then the apply thread finishes entry 1.
	processAppend()
	processApply()

	t.Logf("state machine %q, raft applied %d; the log's state at index 2 is \"ab\"", sm, rn.raft.raftLog.applied)
	require.Equal(t, uint64(2), rn.raft.raftLog.applied)
	require.Equal(t, "aba", string(sm), "divergence reproduced")
}
