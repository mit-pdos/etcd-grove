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

// TestRawNodeStatusAutoLeave ensures that Status reports AutoLeave in a joint
// configuration entered with an implicit transition, as ApplyConfChange's
// ConfState does.
func TestRawNodeStatusAutoLeave(t *testing.T) {
	s := newTestMemoryStorage(withPeers(1))
	rn, err := NewRawNode(newTestConfig(1, 10, 1, s))
	require.NoError(t, err)

	var cs *pb.ConfState
	// stabilize handles each Ready as doc.go describes: persist, apply
	// (ApplyConfChange for conf changes), then Advance.
	stabilize := func() {
		for rn.HasReady() {
			rd := rn.Ready()
			if !IsEmptyHardState(rd.HardState) {
				require.NoError(t, s.SetHardState(rd.HardState))
			}
			require.NoError(t, s.Append(rd.Entries))
			for _, e := range rd.CommittedEntries {
				if e.GetType() == pb.EntryConfChangeV2 {
					cc := &pb.ConfChangeV2{}
					require.NoError(t, proto.Unmarshal(e.GetData(), cc))
					cs = rn.ApplyConfChange(cc)
				}
			}
			rn.Advance(rd)
		}
	}
	require.NoError(t, rn.Campaign())
	stabilize()
	require.Equal(t, StateLeader, rn.Status().RaftState)

	// Enter a joint configuration with auto-leave: add voter 2, which never
	// answers, so the configuration stays joint.
	require.NoError(t, rn.ProposeConfChange(&pb.ConfChangeV2{
		Transition: pb.ConfChangeTransitionJointImplicit.Enum(),
		Changes:    []*pb.ConfChangeSingle{{Type: pb.ConfChangeAddNode.Enum(), NodeId: new(uint64(2))}},
	}))
	stabilize()
	require.NotNil(t, cs)
	require.Equal(t, []uint64{1}, cs.GetVotersOutgoing())
	require.True(t, cs.GetAutoLeave(), "ApplyConfChange's ConfState")

	st := rn.Status()
	assert.Equal(t, []uint64{1}, st.Config.Voters[1].Slice())
	assert.True(t, st.Config.AutoLeave, "Status().Config: %s", st.Config)
}
