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

// A pre-candidate counts a granted MsgPreVoteResp that answers an earlier
// pre-campaign: the response carries the term of that earlier request, which
// equals the node's current term once the node has moved up one term, so Step's
// term check lets it through and stepCandidate tallies it for the current round.
//
// Node 1 (of 1, 2, 3; pre-vote and check-quorum on, as etcd configures raft)
// pre-campaigns at term 1 (MsgPreVote for term 2); node 2's grant (Term 2) is
// delayed. Node 1 then hears from leader 3 of term 2 and follows it. Later it
// pre-campaigns again, at term 2 (MsgPreVote for term 3). The stale grant
// arrives: with node 1's own grant it is a quorum, and node 1 starts a real
// election at term 3 although no peer granted a pre-vote for term 3.
func TestPreVoteStaleGrantFromEarlierRound(t *testing.T) {
	r := newTestRaft(1, 10, 1, newTestMemoryStorage(withPeers(1, 2, 3)))
	r.preVote = true
	r.checkQuorum = true
	r.becomeFollower(1, None)

	// Round 1, at term 1: requests for term 2.
	r.Step(&pb.Message{From: new(uint64(1)), To: new(uint64(1)), Type: pb.MsgHup.Enum()})
	if r.state != StatePreCandidate || r.Term != 1 {
		t.Fatalf("round 1: state %v term %d, want pre-candidate at term 1", r.state, r.Term)
	}
	r.readMessages() // the node's own grant is stepped; the requests go out

	// Leader 3 of term 2: node 1 follows it.
	r.Step(&pb.Message{From: new(uint64(3)), To: new(uint64(1)), Term: new(uint64(2)), Type: pb.MsgHeartbeat.Enum()})
	if r.state != StateFollower || r.Term != 2 || r.lead != 3 {
		t.Fatalf("after heartbeat: state %v term %d lead %d", r.state, r.Term, r.lead)
	}
	r.readMessages()

	// Round 2, at term 2: requests for term 3.
	r.Step(&pb.Message{From: new(uint64(1)), To: new(uint64(1)), Type: pb.MsgHup.Enum()})
	if r.state != StatePreCandidate || r.Term != 2 {
		t.Fatalf("round 2: state %v term %d, want pre-candidate at term 2", r.state, r.Term)
	}
	for _, m := range r.readMessages() {
		if m.GetType() == pb.MsgPreVote && m.GetTerm() != 3 {
			t.Fatalf("round 2 request at term %d, want 3", m.GetTerm())
		}
	}

	// Node 2's delayed grant from round 1 (Term 2, for the term-2 request).
	r.Step(&pb.Message{From: new(uint64(2)), To: new(uint64(1)), Term: new(uint64(2)), Type: pb.MsgPreVoteResp.Enum()})

	if r.state == StateCandidate && r.Term == 3 {
		t.Errorf("stale grant counted: node 1 campaigns at term 3 on a pre-vote granted for term 2")
	}
}

// The same at one term: node 1 pre-campaigns at term 1 (for term 2), hears from
// leader 3 of term 1 and follows it, then pre-campaigns again at term 1. Node 2's
// grant from the first round (Term 2, the term both rounds request) arrives late
// and is counted for the second round, although node 2 has since learnt of the
// leader (and, with check-quorum on, would now ignore the request).
func TestPreVoteStaleGrantSameTerm(t *testing.T) {
	r := newTestRaft(1, 10, 1, newTestMemoryStorage(withPeers(1, 2, 3)))
	r.preVote = true
	r.checkQuorum = true
	r.becomeFollower(1, None)

	r.Step(&pb.Message{From: new(uint64(1)), To: new(uint64(1)), Type: pb.MsgHup.Enum()})
	r.readMessages()
	r.Step(&pb.Message{From: new(uint64(3)), To: new(uint64(1)), Term: new(uint64(1)), Type: pb.MsgHeartbeat.Enum()})
	if r.state != StateFollower || r.Term != 1 || r.lead != 3 {
		t.Fatalf("after heartbeat: state %v term %d lead %d", r.state, r.Term, r.lead)
	}
	r.readMessages()
	r.Step(&pb.Message{From: new(uint64(1)), To: new(uint64(1)), Type: pb.MsgHup.Enum()})
	if r.state != StatePreCandidate || r.Term != 1 {
		t.Fatalf("round 2: state %v term %d", r.state, r.Term)
	}
	r.readMessages()
	r.Step(&pb.Message{From: new(uint64(2)), To: new(uint64(1)), Term: new(uint64(2)), Type: pb.MsgPreVoteResp.Enum()})
	if r.state == StateCandidate && r.Term == 2 {
		t.Errorf("stale grant counted: node 1 campaigns at term 2 on a grant from an earlier round")
	}
}
