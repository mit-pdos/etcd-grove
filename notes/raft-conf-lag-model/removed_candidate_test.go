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

// A candidate whose own removal is applied (ApplyConfChange) while it campaigns stays a
// candidate outside the configuration; if the remaining voters grant it their votes, it wins
// and becomeLeader dereferences its missing Progress: a nil-pointer panic.
//
// An application reaches this state only by calling Advance before ApplyConfChange
// (issues/raft-advance-before-applyconfchange.md): hasUnappliedConfChanges keeps a node with
// a committed but unapplied conf change from campaigning, unless Advance has already moved
// the applied index past it. The test drives the raft struct directly (newTestRaft,
// applyConfChange, Step) to show the code path; the public-API route is the one of
// leaderlag_test.go (Advance, then campaign, then ApplyConfChange).

import (
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

func TestRemovedCandidateWinsAndPanics(t *testing.T) {
	r := newTestRaft(1, 10, 1, newTestMemoryStorage(withPeers(1, 2, 3)))
	r.becomeCandidate() // node 1 campaigns in term 1, voting for itself
	// the application applies "remove 1" (committed earlier, Advanced past)
	r.applyConfChange(pb.ConfChange{Type: pb.ConfChangeRemoveNode, NodeId: 1}.AsV2())
	if r.state != StateCandidate {
		t.Fatalf("state = %v, want candidate", r.state)
	}
	if _, ok := r.trk.Progress[1]; ok {
		t.Fatalf("node 1 still tracked")
	}
	defer func() {
		if e := recover(); e != nil {
			t.Logf("PANIC reproduced: %v", e)
			return
		}
		t.Fatalf("no panic: state = %v", r.state)
	}()
	// nodes 2 and 3, the whole new configuration, grant the vote
	r.Step(pb.Message{From: 2, To: 1, Term: r.Term, Type: pb.MsgVoteResp})
	r.Step(pb.Message{From: 3, To: 1, Term: r.Term, Type: pb.MsgVoteResp})
}
