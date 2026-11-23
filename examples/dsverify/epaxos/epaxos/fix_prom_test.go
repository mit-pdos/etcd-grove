package epaxos

import "testing"

// TestRecoveryStopsAfterPromisingHigherBallot (the model prover's G1): 0 proposes 0.0 (PUT), its
// PreAccepts are lost. 1 recovers 0.0 at ballot 6, 2 at ballot 7; 1 promises 7 to 2 (replies
// NONE). The replies of 0 (pre-accepted at 0) and 4 (NONE) to Prepare(6) then reach 1: a replica
// that has promised 7 takes no part in ballot 6 (Paxos). The parent completes the ballot-6
// recovery anyway: sub-case 5, Phase 1 at 6 with 4 and 0, Accept at 6, 1 commits the PUT; 2
// decides with {2, 1, 3} (all NONE): Phase 1 for a no-op at 7 with 3 and 4, 2 commits the no-op.
func TestRecoveryStopsAfterPromisingHigherBallot(t *testing.T) {
	c := newCluster(t, 5)
	c.propose(0, put(1, "a"))
	c.drop(instOf(0, 0))

	c.recover(1, 0, 0) // 6
	c.recover(2, 0, 0) // 7
	if b1, b2 := c.inst(1, 0, 0).lb.lastTriedBallot, c.inst(2, 0, 0).lb.lastTriedBallot; b1 != 6 || b2 != 7 {
		t.Fatalf("setup: ballots %d, %d", b1, b2)
	}
	c.run(kind("Prepare"), from(2), to(1))
	c.run(kind("Prepare"), from(1), toAny(0, 4))
	for q := int32(0); q < 5; q++ {
		c.r[1].Alive[q] = q == 0 || q == 4
	}
	c.run(kind("PrepareReply"), to(1))
	c.settle(instOf(0, 0), among(0, 1, 4))

	c.run(kind("Prepare"), from(2), to(3))
	c.drop(kind("Prepare"))
	for q := int32(0); q < 5; q++ {
		c.r[2].Alive[q] = q == 3 || q == 4
	}
	c.run(kind("PrepareReply"), to(2))
	c.run(kind("PreAccept"), from(2), to(3))
	c.run(kind("PreAcceptReply"), from(3), to(2))
	c.settle(instOf(0, 0), among(2, 3, 4))
	if !committed(c.inst(2, 0, 0)) {
		t.Fatalf("2 did not commit 0.0: %s", instString(c.inst(2, 0, 0)))
	}
	if e := c.agreementError(); e != "" {
		t.Fatal(e)
	}
}
