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

// TestRawNodeRemoveLastVoter: a single-voter leader accepts a conf change
// removing itself, the only voter; the entry commits, and ApplyConfChange on it
// panics ("removed all voters"), as it would on every node and after a restart.
func TestRawNodeRemoveLastVoter(t *testing.T) {
	s := newTestMemoryStorage(withPeers(1))
	rn, err := NewRawNode(newTestConfig(1, 10, 1, s))
	require.NoError(t, err)

	stabilize := func() {
		for rn.HasReady() {
			rd := rn.Ready()
			if !IsEmptyHardState(rd.HardState) {
				require.NoError(t, s.SetHardState(rd.HardState))
			}
			require.NoError(t, s.Append(rd.Entries))
			for _, e := range rd.CommittedEntries {
				if e.GetType() == pb.EntryConfChange {
					cc := &pb.ConfChange{}
					require.NoError(t, proto.Unmarshal(e.GetData(), cc))
					require.NotPanics(t, func() { rn.ApplyConfChange(cc) }, "applying the committed %v", cc)
				}
			}
			rn.Advance(rd)
		}
	}
	require.NoError(t, rn.Campaign())
	stabilize()
	require.NoError(t, rn.ProposeConfChange(&pb.ConfChange{Type: pb.ConfChangeRemoveNode.Enum(), NodeId: new(uint64(1))}))
	stabilize()
}
