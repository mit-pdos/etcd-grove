package epaxos

import "testing"

// TestLeaderRowCoveredAtAcceptors: 0 proposes 0.0 (PUT k1); its PreAccepts are delayed. 0
// proposes 0.1 (PUT k1, deps[0] = 0); its PreAccepts are lost but the one to 3. Replica 4
// recovers 0.1 with {4, 3, 2}: sub-case 5, Phase 1 with acceptors 1 and 2, which know neither
// instance: 0.1 commits with deps[0] = -1, and everyone learns it. The delayed PreAccepts of 0.0
// then reach 1, 2, 3, which know 0.1: an acceptor must add every interfering instance it knows,
// the leader's row included (0's own row was not complete when it proposed 0.0: 0.1 was
// recovered by others). The parent's acceptors skip row 0 (the ballot's leader is the instance's
// leader): 0.0 commits with deps[0] = -1 and neither instance covers the other.
func TestLeaderRowCoveredAtAcceptors(t *testing.T) {
	c := newCluster(t, 5)
	c.propose(0, put(1, "a"))
	delayed := c.take(instOf(0, 0))
	c.propose(0, put(1, "b"))
	c.run(kind("PreAccept"), from(0), to(3))
	c.drop(instOf(0, 1))

	c.recover(4, 0, 1)
	c.run(kind("Prepare"), from(4), toAny(3, 2))
	c.drop(kind("Prepare"))
	c.r[4].Alive[0], c.r[4].Alive[3] = false, false
	c.run(kind("PrepareReply"), to(4))
	c.settle(instOf(0, 1), among(1, 2, 4))
	if !committed(c.inst(4, 0, 1)) {
		t.Fatalf("setup: 4 did not commit 0.1: %s", instString(c.inst(4, 0, 1)))
	}
	c.r[4].Alive[0], c.r[4].Alive[3] = true, true
	c.r[4].bcastCommit(0, 1)
	c.settle(kind("Commit"))

	for _, m := range delayed {
		c.deliver(m)
	}
	c.settle(instOf(0, 0))
	for i := int32(0); i < 5; i++ {
		if !committed(c.inst(i, 0, 0)) || !committed(c.inst(i, 0, 1)) {
			t.Fatalf("setup: replica %d did not commit both: %s %s", i, instString(c.inst(i, 0, 0)), instString(c.inst(i, 0, 1)))
		}
	}
	if e := c.agreementError(); e != "" {
		t.Fatal(e)
	}
	if e := c.depsError(); e != "" {
		t.Fatal(e)
	}
	// every replica executes them in one order
	for i := int32(0); i < 5; i++ {
		c.execAll(i)
	}
	for i := int32(1); i < 5; i++ {
		if c.value(i, 1) != c.value(0, 1) {
			t.Fatalf("k1 is %q at replica 0 and %q at replica %d", c.value(0, 1), c.value(i, 1), i)
		}
	}
}
