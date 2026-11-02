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

// TestStepWritesAndKeepsCallerMessage: a follower forwarding a proposal to its
// leader writes the To field of the message the caller stepped, and queues that
// same object in its outgoing messages. The test fails if either happens.
func TestStepWritesAndKeepsCallerMessage(t *testing.T) {
	r := newTestRaft(1, 10, 1, newTestMemoryStorage(withPeers(1, 2, 3)))
	r.becomeFollower(1, 2)
	m := &pb.Message{From: new(uint64(3)), To: new(uint64(1)), Type: pb.MsgProp.Enum(),
		Entries: []*pb.Entry{{Data: []byte("x")}}}
	if err := r.Step(m); err != nil {
		t.Fatal(err)
	}
	if m.GetTo() != 1 {
		t.Errorf("the caller's message was written: To = %d, want unchanged 1", m.GetTo())
	}
	for _, out := range r.readMessages() {
		if out == m {
			t.Errorf("the caller's message is queued as an outgoing message")
		}
	}
}
