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
	"google.golang.org/protobuf/proto"

	pb "go.etcd.io/raft/v3/raftpb"
)

// TestRawNodeProposeUnknownTransition: a ConfChangeV2 whose Transition is none
// of the three defined values is accepted by the leader, committed, and panics
// in ApplyConfChange ("unknown transition") on every node that applies it.
func TestRawNodeProposeUnknownTransition(t *testing.T) {
	s := newTestMemoryStorage(withPeers(1))
	rawNode, err := NewRawNode(newTestConfig(1, 10, 1, s))
	require.NoError(t, err)
	stabilize := func() {
		for rawNode.HasReady() {
			rd := rawNode.Ready()
			s.Append(rd.Entries)
			for _, ent := range rd.CommittedEntries {
				if ent.GetType() == pb.EntryConfChangeV2 {
					cc := &pb.ConfChangeV2{}
					require.NoError(t, proto.Unmarshal(ent.GetData(), cc))
					require.NotPanics(t, func() { rawNode.ApplyConfChange(cc) })
				}
			}
			rawNode.Advance(rd)
		}
	}
	require.NoError(t, rawNode.Campaign())
	stabilize()

	require.NoError(t, rawNode.ProposeConfChange(&pb.ConfChangeV2{
		Transition: pb.ConfChangeTransition(7).Enum(),
		Changes: []*pb.ConfChangeSingle{
			{Type: pb.ConfChangeAddNode.Enum(), NodeId: new(uint64(2))},
		},
	}))
	stabilize()
}
