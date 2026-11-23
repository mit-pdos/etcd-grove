package epaxos

import "testing"

// TestRecoveryOwnReplyKeepsItsVbal: replica 0 commits 0.0 (a PUT) on the fast path with its
// other replicas but 3 (its connection to 3 is down), its Commits are lost. Replica 3, which
// never saw 0.0, recovers it with the quorum {3, 1, 2} (its connection to 0 broke). Its own
// PrepareReply must report the ballot of its last vote (none: -1), not the ballot it is
// preparing; the parent's own reply claims a vote at the new ballot, dominates the replies of 1
// and 2, and replica 3 commits a no-op over the committed PUT.
func TestRecoveryOwnReplyKeepsItsVbal(t *testing.T) {
	c := newCluster(t, 5)
	c.r[0].Alive[3] = false
	c.propose(0, put(1, "a"))
	c.settle(kind("PreAccept"))
	c.settle(kind("PreAcceptReply"))
	if !committed(c.inst(0, 0, 0)) {
		t.Fatalf("setup: replica 0 did not commit 0.0")
	}
	c.drop(kind("Commit"))

	c.r[3].Alive[0] = false // replica 3's connection to 0 broke
	c.recover(3, 0, 0)
	if vb := c.inst(3, 0, 0).vbal; vb != -1 {
		t.Errorf("replica 3 never voted in 0.0 but its vbal is %d", vb)
	}
	c.drop(kind("Prepare"), to(4))
	c.settle(not(toAny(0)), not(fromAny(0))) // replica 0 is cut off; 1, 2, 3, 4 talk
	if e := c.agreementError(); e != "" {
		t.Fatal(e)
	}
	if !committed(c.inst(3, 0, 0)) {
		t.Fatalf("replica 3 did not commit 0.0: %s", instString(c.inst(3, 0, 0)))
	}
}
