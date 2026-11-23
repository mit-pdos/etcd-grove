package epaxos

import "testing"

// TestPrepareReplyCarriesVBallot: replica 1 proposes 1.0 (initial ballot 1); replica 2
// pre-accepts it (vbal 1); replica 3 starts recovering 1.0 and replica 2 answers its Prepare. The
// PrepareReply that reaches replica 3 must carry replica 2's vbal (the parent's Marshal skips
// VBallot: replica 3 reads 0).
func TestPrepareReplyCarriesVBallot(t *testing.T) {
	c := newCluster(t, 5)
	c.propose(1, put(1, "a"))
	c.run(kind("PreAccept"), to(2))
	if vb := c.inst(2, 1, 0).vbal; vb != 1 {
		t.Fatalf("setup: replica 2's vbal is %d", vb)
	}
	c.recover(3, 1, 0)
	c.run(kind("Prepare"), to(2))
	reps := c.take(kind("PrepareReply"), from(2), to(3))
	if len(reps) != 1 {
		t.Fatalf("expected one PrepareReply from 2, got %d", len(reps))
	}
	if vb := reps[0].msg.(*PrepareReply).VBallot; vb != 1 {
		t.Fatalf("replica 2's PrepareReply reports vbal %d, its vbal is 1", vb)
	}
}
