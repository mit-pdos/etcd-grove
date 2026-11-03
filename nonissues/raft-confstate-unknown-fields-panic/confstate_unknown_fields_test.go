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
	"google.golang.org/protobuf/encoding/protowire"

	pb "go.etcd.io/raft/v3/raftpb"
)

// TestRestoreFromSnapMsgUnknownField ensures that a follower restores a
// snapshot whose ConfState has a field this version does not know, as a
// snapshot from a newer version may have. (The fork branch
// fix/raft-confstate-unknown-fields-panic adds it to raft_test.go.)
func TestRestoreFromSnapMsgUnknownField(t *testing.T) {
	cs := &pb.ConfState{Voters: []uint64{1, 2}}
	cs.ProtoReflect().SetUnknown(protowire.AppendVarint(protowire.AppendTag(nil, 99, protowire.VarintType), 1))
	s := &pb.Snapshot{
		Metadata: &pb.SnapshotMetadata{
			Index:     new(uint64(11)),
			Term:      new(uint64(11)),
			ConfState: cs,
		},
	}
	m := &pb.Message{Type: pb.MsgSnap.Enum(), From: new(uint64(1)), Term: new(uint64(2)), Snapshot: s}

	sm := newTestRaft(2, 10, 1, newTestMemoryStorage(withPeers(1, 2)))
	sm.Step(m)

	assert.Equal(t, uint64(11), sm.raftLog.lastIndex())
}
