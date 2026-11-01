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

	pb "go.etcd.io/raft/v3/raftpb"
)

// TestRawNodeAsyncSnapshotDuringApply ensures that, with AsyncStorageWrites, a
// follower that receives a snapshot while committed entries before it are being
// applied ends with the snapshot's state, when the append thread applies the
// snapshot and runs ahead of the apply thread.
func TestRawNodeAsyncSnapshotDuringApply(t *testing.T) {
	s := newTestMemoryStorage(withPeers(1, 2, 3))
	cfg := newTestConfig(2, 10, 1, s)
	cfg.AsyncStorageWrites = true
	rawNode, err := NewRawNode(cfg)
	require.NoError(t, err)

	var state []byte // the state machine: the data of the entries applied
	var appendWork, applyWork []*pb.Message
	ready := func() {
		for _, m := range rawNode.Ready().Messages {
			switch m.GetTo() {
			case LocalAppendThread:
				appendWork = append(appendWork, m)
			case LocalApplyThread:
				applyWork = append(applyWork, m)
			}
		}
	}
	respond := func(m *pb.Message) {
		for _, r := range m.GetResponses() {
			if r.GetTo() == 2 {
				require.NoError(t, rawNode.Step(r))
			}
		}
	}
	// The append thread processes everything it has before the apply thread
	// does.
	stabilize := func() {
		for rawNode.HasReady() || len(appendWork) > 0 || len(applyWork) > 0 {
			ready()
			for len(appendWork) > 0 {
				m := appendWork[0]
				appendWork = appendWork[1:]
				if snap := m.GetSnapshot(); snap != nil {
					require.NoError(t, s.ApplySnapshot(snap))
					state = append([]byte(nil), snap.GetData()...)
				}
				require.NoError(t, s.Append(m.GetEntries()))
				respond(m)
				ready()
			}
			if len(applyWork) > 0 {
				m := applyWork[0]
				applyWork = applyWork[1:]
				for _, e := range m.GetEntries() {
					state = append(state, e.GetData()...)
				}
				respond(m)
			}
		}
	}

	// Leader 1 commits "a" at index 1. Its snapshot at index 2, with state
	// "ab", arrives before the apply thread applies index 1.
	require.NoError(t, rawNode.Step(&pb.Message{From: new(uint64(1)), To: new(uint64(2)), Term: new(uint64(1)),
		Type: pb.MsgApp.Enum(), Index: new(uint64(0)), LogTerm: new(uint64(0)), Commit: new(uint64(1)),
		Entries: []*pb.Entry{{Term: new(uint64(1)), Index: new(uint64(1)), Data: []byte("a")}}}))
	ready()
	for len(appendWork) > 0 {
		m := appendWork[0]
		appendWork = appendWork[1:]
		require.NoError(t, s.Append(m.GetEntries()))
		respond(m)
		ready()
	}
	require.Len(t, applyWork, 1)
	require.NoError(t, rawNode.Step(&pb.Message{From: new(uint64(1)), To: new(uint64(2)), Term: new(uint64(1)),
		Type: pb.MsgSnap.Enum(), Snapshot: &pb.Snapshot{Data: []byte("ab"), Metadata: &pb.SnapshotMetadata{
			Index: new(uint64(2)), Term: new(uint64(1)), ConfState: &pb.ConfState{Voters: []uint64{1, 2, 3}}}}}))
	stabilize()

	assert.Equal(t, "ab", string(state))
}
