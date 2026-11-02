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

	"github.com/stretchr/testify/require"
	"google.golang.org/protobuf/proto"

	pb "go.etcd.io/raft/v3/raftpb"
)

// TestReadOnlyForRemovedLeader ensures that the read index of a leader that
// removed itself includes the entries the remaining voter has committed since.
func TestReadOnlyForRemovedLeader(t *testing.T) {
	nt := newNetwork(nil, nil)
	nt.send(&pb.Message{From: new(uint64(2)), To: new(uint64(2)), Type: pb.MsgHup.Enum()})
	a, b := nt.peers[1].(*raft), nt.peers[2].(*raft)

	// Peer 2 removes itself (index 2), and both peers apply the removal once it
	// commits. Peer 2 stays leader.
	cc := &pb.ConfChange{Type: pb.ConfChangeRemoveNode.Enum(), NodeId: new(uint64(2))}
	ccData, err := proto.Marshal(cc)
	require.NoError(t, err)
	nt.send(&pb.Message{From: new(uint64(2)), To: new(uint64(2)), Type: pb.MsgProp.Enum(), Entries: []*pb.Entry{{Type: pb.EntryConfChange.Enum(), Data: ccData}}})
	require.Equal(t, uint64(2), a.raftLog.committed)
	require.Equal(t, uint64(2), b.raftLog.committed)
	a.applyConfChange(cc.AsV2())
	b.applyConfChange(cc.AsV2())

	// Peer 1, now the only voter, becomes leader and commits y.
	a.becomeCandidate()
	a.becomeLeader()
	nt.send(&pb.Message{From: new(uint64(1)), To: new(uint64(1)), Type: pb.MsgProp.Enum(), Entries: []*pb.Entry{{Data: []byte("y")}}})
	y := a.raftLog.lastIndex()
	require.Equal(t, y, a.raftLog.committed)

	// Ensure the read index of a read issued now at peer 2 includes y.
	wctx := []byte("ctx")
	nt.send(&pb.Message{From: new(uint64(2)), To: new(uint64(2)), Type: pb.MsgReadIndex.Enum(), Entries: []*pb.Entry{{Data: wctx}}})
	for _, rs := range b.readStates {
		if slices.Equal(rs.RequestCtx, wctx) {
			require.GreaterOrEqual(t, rs.Index, y, "read index")
		}
	}
}
