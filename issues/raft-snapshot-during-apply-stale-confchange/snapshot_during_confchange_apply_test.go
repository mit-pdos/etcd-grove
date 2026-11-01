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
	"fmt"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"

	pb "go.etcd.io/raft/v3/raftpb"
)

// TestRawNodeSnapshotDuringConfChangeApply ensures that a follower that receives
// a snapshot while the application is applying a conf change the snapshot covers
// ends with the snapshot's configuration, and that ApplyConfChange returns the
// configuration at the conf change's index.
func TestRawNodeSnapshotDuringConfChangeApply(t *testing.T) {
	for i, tt := range []struct {
		cc     pb.ConfChangeI
		cs     *pb.ConfState // the snapshot's, at index 2
		voters [2][]uint64   // the configuration at index 1
	}{
		// "add 4" at index 1, then "remove 4" at index 2.
		{&pb.ConfChange{Type: pb.ConfChangeAddNode.Enum(), NodeId: new(uint64(4))},
			&pb.ConfState{Voters: []uint64{1, 2, 3}},
			[2][]uint64{{1, 2, 3, 4}, nil}},
		// "add 4" entering a joint configuration at index 1, still joint at index 2.
		{&pb.ConfChangeV2{Transition: pb.ConfChangeTransitionJointExplicit.Enum(),
			Changes: []*pb.ConfChangeSingle{{Type: pb.ConfChangeAddNode.Enum(), NodeId: new(uint64(4))}}},
			&pb.ConfState{Voters: []uint64{1, 2, 3, 4}, VotersOutgoing: []uint64{1, 2, 3}},
			[2][]uint64{{1, 2, 3, 4}, {1, 2, 3}}},
	} {
		t.Run(fmt.Sprint(i), func(t *testing.T) {
			s := newTestMemoryStorage(withPeers(1, 2, 3))
			rawNode, err := NewRawNode(newTestConfig(2, 10, 1, s))
			require.NoError(t, err)
			typ, data, err := pb.MarshalConfChange(tt.cc)
			require.NoError(t, err)
			snap := &pb.Message{From: new(uint64(1)), To: new(uint64(2)), Term: new(uint64(1)), Type: pb.MsgSnap.Enum(),
				Snapshot: &pb.Snapshot{Metadata: &pb.SnapshotMetadata{Index: new(uint64(2)), Term: new(uint64(1)), ConfState: tt.cs}}}

			var cs *pb.ConfState
			// apply applies committed entries, calling ApplyConfChange for
			// the conf change.
			apply := func(ents []*pb.Entry) {
				for _, e := range ents {
					if e.GetType() == typ {
						cs = rawNode.ApplyConfChange(tt.cc)
					}
				}
			}
			// Leader 1 commits the conf change at index 1, and the
			// application starts applying it. Its snapshot at index 2
			// arrives before the application calls ApplyConfChange.
			require.NoError(t, rawNode.Step(&pb.Message{From: new(uint64(1)), To: new(uint64(2)), Term: new(uint64(1)),
				Type: pb.MsgApp.Enum(), Index: new(uint64(0)), LogTerm: new(uint64(0)), Commit: new(uint64(1)),
				Entries: []*pb.Entry{{Term: new(uint64(1)), Index: new(uint64(1)), Type: typ.Enum(), Data: data}}}))
			rd := rawNode.Ready()
			require.Len(t, rd.CommittedEntries, 1)
			require.NoError(t, s.Append(rd.Entries))
			require.NoError(t, rawNode.Step(snap))
			apply(rd.CommittedEntries)
			rawNode.Advance(rd)
			// Leader 1 sends the snapshot again if the follower ignored it.
			require.NoError(t, rawNode.Step(snap))
			for rawNode.HasReady() {
				rd := rawNode.Ready()
				if !IsEmptySnap(rd.Snapshot) {
					require.NoError(t, s.ApplySnapshot(rd.Snapshot))
				}
				require.NoError(t, s.Append(rd.Entries))
				apply(rd.CommittedEntries)
				rawNode.Advance(rd)
			}

			require.NotNil(t, cs)
			assert.Equal(t, tt.voters[0], cs.GetVoters())
			assert.Equal(t, tt.voters[1], cs.GetVotersOutgoing())
			assert.Equal(t, tt.cs.GetVoters(), rawNode.raft.trk.Voters[0].Slice())
			assert.Equal(t, tt.cs.GetVotersOutgoing(), rawNode.raft.trk.Voters[1].Slice())
		})
	}
}
