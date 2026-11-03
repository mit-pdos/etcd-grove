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

// TestReadOnlyForNewSingleVoterLeader ensures that the read index of a leader
// whose configuration was reduced to itself by a removal includes the entries
// committed before the read.
func TestReadOnlyForNewSingleVoterLeader(t *testing.T) {
	nt := newNetwork(nil, nil)
	nt.send(&pb.Message{From: new(uint64(2)), To: new(uint64(2)), Type: pb.MsgHup.Enum()})
	a, b := nt.peers[1].(*raft), nt.peers[2].(*raft)

	// Peer 2 proposes its removal (index 2) and x (index 3), and commits both;
	// peer 1 learns that the removal is committed, but not x. Both peers then
	// apply the removal.
	cc := &pb.ConfChange{Type: pb.ConfChangeRemoveNode.Enum(), NodeId: new(uint64(2))}
	ccData, err := proto.Marshal(cc)
	require.NoError(t, err)
	nt.msgHook = func(m *pb.Message) bool { return m.GetTo() != 1 || m.GetCommit() < 3 }
	nt.send(
		&pb.Message{From: new(uint64(2)), To: new(uint64(2)), Type: pb.MsgProp.Enum(), Entries: []*pb.Entry{{Type: pb.EntryConfChange.Enum(), Data: ccData}}},
		&pb.Message{From: new(uint64(2)), To: new(uint64(2)), Type: pb.MsgProp.Enum(), Entries: []*pb.Entry{{Data: []byte("x")}}},
	)
	require.Equal(t, uint64(2), a.raftLog.committed)
	require.Equal(t, uint64(3), b.raftLog.committed)
	a.applyConfChange(cc.AsV2())
	b.applyConfChange(cc.AsV2())

	// Peer 1, now the only voter, becomes leader.
	a.becomeCandidate()
	a.becomeLeader()

	// Ensure the read index of a read issued now includes x.
	wctx := []byte("ctx")
	nt.send(&pb.Message{From: new(uint64(1)), To: new(uint64(1)), Type: pb.MsgReadIndex.Enum(), Entries: []*pb.Entry{{Data: wctx}}})
	i := slices.IndexFunc(a.readStates, func(rs ReadState) bool { return slices.Equal(rs.RequestCtx, wctx) })
	require.NotEqual(t, -1, i, "no read state for the read")
	require.GreaterOrEqual(t, a.readStates[i].Index, uint64(3), "read index")
}
