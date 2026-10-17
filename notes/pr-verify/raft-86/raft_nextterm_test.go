package raft

import (
	"math"
	"testing"

	pb "go.etcd.io/raft/v3/raftpb"
)

// In the last epoch (Term >= 2^64 - 2^16) nextTerm wraps: becomeCandidate moves the term
// backwards, to the 16-bit draw alone. (Before the PR, r.Term+1 wrapped only at 2^64-1.)
func TestNextTermWrapsInLastEpoch(t *testing.T) {
	r := newTestRaft(1, 10, 1, newTestMemoryStorage(withPeers(1, 2, 3)))
	old := uint64(math.MaxUint64 - 1000)
	r.becomeFollower(old, None)
	r.becomeCandidate()
	if r.Term >= old {
		t.Fatalf("term %d did not wrap below %d", r.Term, old)
	}
	if r.Term >= 1<<16 {
		t.Fatalf("term %d is not the draw alone", r.Term)
	}
	t.Logf("becomeCandidate at term %d moved to term %d", old, r.Term)
}

// Below the last epoch the new term is the next epoch with a random low half: later than the
// old one by less than 2^17.
func TestNextTermBounds(t *testing.T) {
	for _, old := range []uint64{0, 1, 0xffff, 0x10000, 0x1ffff, math.MaxUint64 - 0x10000} {
		for i := 0; i < 100; i++ {
			r := newTestRaft(1, 10, 1, newTestMemoryStorage(withPeers(1, 2, 3)))
			r.becomeFollower(old, None)
			r.becomeCandidate()
			if !(old < r.Term && r.Term-old < 1<<17 && r.Term>>16 == old>>16+1) {
				t.Fatalf("term %d -> %d", old, r.Term)
			}
		}
	}
}

// A pre-vote's term and the election's that follows are independent draws: the election's
// may be lower than the term the pre-vote was granted at.
func TestPreVoteTermDiffersFromElectionTerm(t *testing.T) {
	differ, lower := 0, 0
	for i := 0; i < 200; i++ {
		r := newTestRaft(1, 10, 1, newTestMemoryStorage(withPeers(1, 2, 3)))
		r.preVote = true
		r.becomeFollower(5, None)
		r.campaign(campaignPreElection)
		msgs := r.readMessages()
		var pvTerm uint64
		for _, m := range msgs {
			if m.Type == pb.MsgPreVote {
				pvTerm = m.Term
			}
		}
		r.becomeCandidate()
		if r.Term != pvTerm {
			differ++
		}
		if r.Term < pvTerm {
			lower++
		}
	}
	t.Logf("of 200 pre-elections: election term != pre-vote term %d times, lower %d times", differ, lower)
	if differ == 0 {
		t.Fatalf("expected the terms to differ")
	}
}
