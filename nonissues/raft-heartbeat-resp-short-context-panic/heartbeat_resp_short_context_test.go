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

	pb "go.etcd.io/raft/v3/raftpb"
)

// TestHeartbeatRespShortContext steps, into a leader using ReadOnlySafe (the
// default), a MsgHeartbeatResp whose Context is non-empty but shorter than the
// 8 bytes heartbeatCtx writes. The leader should not panic on it.
func TestHeartbeatRespShortContext(t *testing.T) {
	r := newTestRaft(1, 10, 1, newTestMemoryStorage(withPeers(1, 2, 3)))
	r.becomeCandidate()
	r.becomeLeader()
	defer func() {
		if p := recover(); p != nil {
			t.Fatalf("leader panicked: %v", p)
		}
	}()
	_ = r.Step(&pb.Message{Type: pb.MsgHeartbeatResp.Enum(), From: new(uint64(2)), To: new(uint64(1)),
		Term: new(r.Term), Context: []byte{1}})
}
