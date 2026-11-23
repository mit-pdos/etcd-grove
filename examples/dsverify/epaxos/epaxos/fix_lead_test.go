package epaxos

import "testing"

// TestLeaderStopsAfterPromisingHigherBallot: replica 0 proposes 0.0 (PUT k1); 1 and 2
// pre-accept it, their replies are delayed. Replica 3, which knows its own 3.0 (PUT k1), recovers
// 0.0 with {3, 0, 4}: the leader replied, so sub-case 5 runs Phase 1 again (deps[3] = 0). Having
// promised 3's ballot, 0 must not take part in its old ballot any more: on the parent the late
// replies make 0 fast-commit deps[3] = -1 while 3 commits deps[3] = 0.
func TestLeaderStopsAfterPromisingHigherBallot(t *testing.T) {
	c := newCluster(t, 5)
	c.propose(3, put(1, "z"))
	c.drop(instOf(3, 0))
	c.propose(0, put(1, "a"))
	c.run(kind("PreAccept"), from(0), toAny(1, 2))
	c.drop(kind("PreAccept"), from(0))
	late := c.take(kind("PreAcceptReply"), to(0))

	c.recover(3, 0, 0)
	c.run(kind("Prepare"), from(3), toAny(0, 4))
	c.drop(kind("Prepare"))
	c.r[3].Alive[0] = false
	c.run(kind("PrepareReply"), to(3))

	for _, m := range late {
		c.deliver(m)
	}
	c.settle(not(toAny(0)), not(fromAny(0)))
	if !committed(c.inst(3, 0, 0)) {
		t.Fatalf("replica 3 did not commit 0.0: %s", instString(c.inst(3, 0, 0)))
	}
	if e := c.agreementError(); e != "" {
		t.Fatal(e)
	}
}
