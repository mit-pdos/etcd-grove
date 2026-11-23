package epaxos

import "testing"

// TestLeaderMergesItsOwnRow: (A..E = 0..4) 0 proposes x = 0.0 [PUT k1, PUT k2] (its PreAccepts to
// 1, 2, 3 delayed) and y = 0.1 [GET k1] (only 1 gets its PreAccept). 1's executor recovers x (its
// Prepares lost: 1 now rejects PreAccept(x)) and y with {1, 2, 3}: sub-case 5, Phase 1 with 3 and
// 4, which know nothing of x: y commits with deps[0] = -1; 2 does not learn y. 4's z = 4.0 [PUT
// k2] reaches only 3. PreAccept(x) reaches 2 (deps[0] = -1) and 3 (deps[0] = 1: it knows y;
// deps[4] = 0): the replies differ, slow path. The committed attributes are the union of the
// replies (EPaxos Phase 1/2): the parent's mergeAttributes skips the leader's own row and x
// commits with deps[0] = -1: x and y interfere and neither covers the other.
func TestLeaderMergesItsOwnRow(t *testing.T) {
	c := newCluster(t, 5)
	c.propose(0, put(1, "a"), put(2, "b"))
	delayed := c.take(instOf(0, 0))
	c.propose(0, get(1))
	c.run(kind("PreAccept"), from(0), to(1))
	c.drop(instOf(0, 1))

	c.recover(1, 0, 0) // raises 1's ballot for x
	c.drop(kind("Prepare"))
	c.recover(1, 0, 1)
	c.run(kind("Prepare"), from(1), toAny(2, 3))
	c.drop(kind("Prepare"))
	c.r[1].Alive[2] = false
	c.run(kind("PrepareReply"), to(1))
	c.run(kind("PreAccept"), from(1), toAny(3, 4))
	c.drop(kind("PreAccept"))
	c.settle(instOf(0, 1), among(1, 3, 4))
	if !committed(c.inst(1, 0, 1)) {
		t.Fatalf("setup: 1 did not commit y: %s", instString(c.inst(1, 0, 1)))
	}
	c.r[1].Alive[2] = true
	c.r[1].bcastCommit(0, 1)
	c.run(kind("Commit"), toAny(0, 3, 4))
	c.drop(kind("Commit"))

	c.r[4].Alive[0], c.r[4].Alive[1], c.r[4].Alive[2] = false, false, false
	c.propose(4, put(2, "z"))
	c.run(kind("PreAccept"), from(4), to(3))
	c.drop(instOf(4, 0))

	for _, m := range delayed {
		c.deliver(m) // 1 rejects
	}
	c.r[0].Alive[1] = false
	c.run(kind("PreAcceptReply"), from(2), to(0))
	c.run(kind("PreAcceptReply"), from(3), to(0))
	c.settle(instOf(0, 0), among(0, 2, 3))
	if !committed(c.inst(0, 0, 0)) {
		t.Fatalf("setup: 0 did not commit x: %s", instString(c.inst(0, 0, 0)))
	}
	if e := c.agreementError(); e != "" {
		t.Fatal(e)
	}
	if e := c.depsError(); e != "" {
		t.Fatal(e)
	}
}
