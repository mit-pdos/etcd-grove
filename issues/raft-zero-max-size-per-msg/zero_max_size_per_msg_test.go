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
	"bytes"
	"testing"

	"github.com/stretchr/testify/require"
	"google.golang.org/protobuf/proto"

	pb "go.etcd.io/raft/v3/raftpb"
)

// TestRawNodeZeroMaxSizePerMsg runs a single-node cluster configured with
// MaxSizePerMsg 0, which Config documents as "at most one entry per message",
// and MaxCommittedSizePerReady left unset. A proposal should be committed and
// applied.
func TestRawNodeZeroMaxSizePerMsg(t *testing.T) {
	s := NewMemoryStorage()
	rn, err := NewRawNode(&Config{
		ID:              1,
		ElectionTick:    10,
		HeartbeatTick:   1,
		Storage:         s,
		MaxSizePerMsg:   0,
		MaxInflightMsgs: 256,
	})
	require.NoError(t, err)
	require.NoError(t, rn.Bootstrap([]Peer{{ID: 1}}))

	applied := false
	stabilize := func() {
		for rn.HasReady() {
			rd := rn.Ready()
			require.NoError(t, s.Append(rd.Entries))
			for _, e := range rd.CommittedEntries {
				switch e.GetType() {
				case pb.EntryConfChange:
					cc := &pb.ConfChange{}
					require.NoError(t, proto.Unmarshal(e.GetData(), cc))
					rn.ApplyConfChange(cc)
				case pb.EntryNormal:
					if bytes.Equal(e.GetData(), []byte("x")) {
						applied = true
					}
				}
			}
			rn.Advance(rd)
		}
	}
	require.NotPanics(t, func() {
		stabilize()
		require.NoError(t, rn.Campaign())
		stabilize()
		require.NoError(t, rn.Propose([]byte("x")))
		stabilize()
	})
	require.True(t, applied, "the proposal was not applied")
}
