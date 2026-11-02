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
	"slices"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"google.golang.org/protobuf/proto"

	pb "go.etcd.io/raft/v3/raftpb"
)

// TestRawNodeReadIndexJointSelfQuorum ensures that a ReadOnlySafe read at a
// leader that alone is a quorum of its joint configuration ({1}&&{1}, with a
// learner 2 being added) is answered without any other node's response, as at
// the single voter {1}.
func TestRawNodeReadIndexJointSelfQuorum(t *testing.T) {
	s := newTestMemoryStorage(withPeers(1))
	rn, err := NewRawNode(newTestConfig(1, 10, 1, s))
	require.NoError(t, err)

	var readStates []ReadState
	// stabilize handles each Ready as doc.go describes; messages to node 2,
	// which is unreachable, are dropped.
	stabilize := func() {
		for rn.HasReady() {
			rd := rn.Ready()
			if !IsEmptyHardState(rd.HardState) {
				require.NoError(t, s.SetHardState(rd.HardState))
			}
			require.NoError(t, s.Append(rd.Entries))
			readStates = append(readStates, rd.ReadStates...)
			for _, e := range rd.CommittedEntries {
				if e.GetType() == pb.EntryConfChangeV2 {
					cc := &pb.ConfChangeV2{}
					require.NoError(t, proto.Unmarshal(e.GetData(), cc))
					rn.ApplyConfChange(cc)
				}
			}
			rn.Advance(rd)
		}
	}
	require.NoError(t, rn.Campaign())
	stabilize()

	// Add learner 2 through an explicit joint configuration: voters {1}&&{1}.
	require.NoError(t, rn.ProposeConfChange(&pb.ConfChangeV2{
		Transition: pb.ConfChangeTransitionJointExplicit.Enum(),
		Changes:    []*pb.ConfChangeSingle{{Type: pb.ConfChangeAddLearnerNode.Enum(), NodeId: new(uint64(2))}},
	}))
	stabilize()
	st := rn.Status()
	require.Equal(t, StateLeader, st.RaftState)
	require.Equal(t, []uint64{1}, st.Config.Voters[0].Slice())
	require.Equal(t, []uint64{1}, st.Config.Voters[1].Slice())

	wctx := []byte("ctx")
	rn.ReadIndex(wctx)
	stabilize()
	assert.True(t, slices.ContainsFunc(readStates, func(rs ReadState) bool { return slices.Equal(rs.RequestCtx, wctx) }),
		"no read state for a read at a leader that alone is a quorum of %s", st.Config)
}
