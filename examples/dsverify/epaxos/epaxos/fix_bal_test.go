package epaxos

import "testing"

// TestLeaderRecoveryUsesFreshBallot: replica 0 proposes 0.0 (PUT k1) and its PreAccepts to 1
// and 2 are delayed; it then learns 4.0 (PUT k1) and its executor starts recovering 0.0. The
// recovery's ballot must be a fresh ballot owned by 0, above every ballot 0 has seen for 0.0 and
// not the initial one: on the parent it is ballot 0, the initial ballot, so the delayed replies
// of the first Phase 1 count for the recovery's Phase 1 and 0 fast-commits the old attributes
// (deps[4] = -1), while 1 and 2 hold the new ones (deps[4] = 0), which a later recovery by 3
// commits. Also, a replica that recovers an instance a second time must not reuse its ballot.
func TestLeaderRecoveryUsesFreshBallot(t *testing.T) {
	c := newCluster(t, 5)
	c.propose(0, put(1, "a"))
	first := c.take(kind("PreAccept"), from(0)) // delayed

	c.propose(4, put(1, "z"))
	c.run(kind("PreAccept"), from(4), to(0))
	c.drop(kind("PreAccept"), from(4))
	c.drop(kind("PreAcceptReply"))

	c.recover(0, 0, 0)
	if b := c.inst(0, 0, 0).lb.lastTriedBallot; b%5 != 0 || b <= 0 {
		t.Errorf("replica 0 recovers 0.0 at ballot %d (initial ballot 0)", b)
	}
	c.run(kind("Prepare"), toAny(3, 4))
	c.drop(kind("Prepare"))
	c.run(kind("PrepareReply"))
	second := c.take(kind("PreAccept"), from(0))

	for _, m := range first {
		if m.to == 1 || m.to == 2 {
			c.deliver(m)
		}
	}
	c.run(kind("PreAcceptReply"), to(0))
	for _, m := range second {
		if m.to == 1 || m.to == 2 {
			c.deliver(m)
		}
	}
	c.run(kind("PreAcceptReply"), to(0))
	c.drop(kind("Commit"))
	c.drop(kind("Accept"))

	c.r[3].Alive[0] = false
	c.recover(3, 0, 0)
	c.drop(kind("Prepare"), to(4))
	c.settle(not(toAny(0)), not(fromAny(0)))
	c.settle()
	if e := c.agreementError(); e != "" {
		t.Fatal(e)
	}

	// a replica that recovers an instance twice (its executor asks again) uses two ballots
	c.recover(3, 1, 0)
	b1 := c.inst(3, 1, 0).lb.lastTriedBallot
	c.recover(3, 1, 0)
	if b2 := c.inst(3, 1, 0).lb.lastTriedBallot; b2 <= b1 || b2%5 != 3 {
		t.Fatalf("replica 3 recovers 1.0 again at ballot %d after ballot %d", b2, b1)
	}
}
