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

package rafthttp

import (
	"strings"
	"testing"

	"go.etcd.io/etcd/server/v3/etcdserver/api/snap"
	"go.etcd.io/raft/v3/raftpb"
)

// TestSnapshotSendLongerThanDeclared: TestSnapshotSend's case #3 alone (5 bytes sent, 1
// declared), which that test does not reach once case #2 fails.
func TestSnapshotSendLongerThanDeclared(t *testing.T) {
	m := &raftpb.Message{Type: raftpb.MsgSnap.Enum(), To: new(uint64(1)), Snapshot: &raftpb.Snapshot{}}
	sent, files := testSnapshotSend(t, snap.NewMessage(m, strReaderCloser{strings.NewReader("hello")}, 1))
	if sent || len(files) != 0 {
		t.Errorf("5 bytes sent for a declared 1: sent=%v, %d file(s) kept", sent, len(files))
	}
}
