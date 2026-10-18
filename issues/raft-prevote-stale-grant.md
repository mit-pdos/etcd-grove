---
upstream: unchecked
links:
---

# raft: a pre-candidate counts a pre-vote granted in an earlier pre-campaign

- **Status**: a bug in pre-vote's guarantee (not in safety): a delayed `MsgPreVoteResp` from an
  earlier pre-campaign is tallied for the current one, so a node can start a real election
  (raise its term) on pre-votes the peers did not grant for this round -- the disruption
  pre-vote exists to prevent. Reproduced by two Go tests (below). Not reported upstream; upstream
  not searched.
- **Where** (etcd-io/raft v3.7.0 `b867cf13` as in the fork's `raft37-goose-lean` `509271dac`,
  the revision `etc/goose.py` pins; line numbers of that tree):
  - `raft.go:1097-1166` (`Step`'s term check): a `MsgPreVoteResp` of a term equal to the node's
    goes on to `r.step`; a granted one of a higher term is let through without a term change
    (`raft.go:1117`).
  - `raft.go:1665-1689` (`stepCandidate`): at a pre-candidate every `MsgPreVoteResp` is
    `myVoteRespType` and is polled, whatever its term; nothing ties a response to the
    pre-campaign that sent the request (a pre-vote request and its response carry only the term
    requested, `m.Term`).
  - `raft.go:917-930` (`becomePreCandidate`): resets the tally (`trk.ResetVotes()`), so only a
    response that *arrives* during the new round is counted -- which a delayed one does.
  - `tracker/tracker.go:251` (`RecordVote`): the first response from a peer in a round wins.
- **What happens**: two shapes.
  1. *Across a term.* Node 1 pre-campaigns at term 1 (`MsgPreVote` for term 2); node 2 grants
     (`MsgPreVoteResp`, `Term: 2`), but the grant is delayed. Node 1 hears from leader 3 of term 2
     and follows it. Its election timer later fires (it lost contact with 3) and it pre-campaigns
     at term 2 (requests for term 3). Node 2's old grant arrives: its `Term` (2) equals node 1's,
     so `Step` passes it to `stepCandidate`, which counts it; with node 1's own grant that is a
     quorum of three, and node 1 becomes a candidate at term 3. Node 2, which follows leader 3,
     would have refused (or, with check-quorum, ignored) the term-3 pre-vote.
  2. *At one term.* Node 1 pre-campaigns at term 1 (for term 2), hears from leader 3 of term 1
     (a pre-candidate becomes a follower on its leader's heartbeat), and later pre-campaigns again
     at term 1. Node 2's grant from the first round (`Term: 2`, the term both rounds request) is
     counted for the second, although node 2 has learnt of leader 3 meanwhile.

  In both, node 1's term rises past the leader's; when node 1 next hears from the leader it answers
  the stale `MsgApp`/heartbeat with a `MsgAppResp` of its higher term, and the leader steps down.
  Reproduction (in package `raft`, next to `raft_test.go`; both tests fail at the pinned revision):

  ```go
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
  ```

  `PATH=/usr/local/go/bin:$PATH GOTOOLCHAIN=go1.27.1 go test -run TestPreVoteStaleGrant .`:
  `stale grant counted: node 1 campaigns at term 3 on a pre-vote granted for term 2` and
  `... campaigns at term 2 on a grant from an earlier round`.

  Reachability: it needs a response delayed past a leader election and an election timeout (a
  reconnect of the peer stream, a slow network); messages are not otherwise ordered across peers.
- **Expected**: the documentation of `Config.PreVote` (`raft.go:228-231`): pre-vote "prevents
  disruption when a node that has been partitioned away rejoins the cluster"; the thesis (9.6):
  a candidate starts the real election only if it learns from a majority that it *could* win
  it -- of the current round.
- **How the proof handles it**: not a safety question: the model admits any pre-vote response
  (`Step.sendFree`, and a pre-candidate's tally is invisible to the protocol, `toPState`), and the
  real election still needs real votes (`Step.campaign`, `Step.win`). The `RawNode` layer has so
  far required pre-vote off (`ownRawNode`'s `Hpvoff`); the term budget of the coming pre-vote stage
  must cover shape 1's term rise past the message's term (notes/STATUS.md, "Raft: CheckQuorum and
  PreVote on").
- **Possible fixes**: shape 1: at a pre-candidate count only granted responses with `Term ==
  r.Term + 1` (in `stepCandidate`, or drop them in `Step`'s `m.Term == r.Term` case at a
  pre-candidate); a rejection of the current round carries a term at least `r.Term`. Shape 2 needs
  the response to identify the round (e.g. echo a per-round nonce in `Context`, as read-index
  requests do), since both rounds request the same term.
- **Found**: 2026-10-17, while planning pre-vote's term budget at the `RawNode` layer (a won
  pre-vote at `term + 1` past the message's term, which the budget cannot otherwise justify);
  reproduced with the tests above.
