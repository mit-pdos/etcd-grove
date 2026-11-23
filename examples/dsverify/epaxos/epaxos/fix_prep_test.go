package epaxos

import "testing"

// TestRecoveryCommittedReplyWins: 0 fast-commits 0.0 (PUT k1, deps[4] = -1) with 1, 2 (and 3:
// its thrifty PreAccepts reach all but 4); its Commits are lost. Replica 4, which knows its own
// 4.0 (PUT k1), recovers 0.0 with {4, 0, 1}; 0's "committed" reply arrives before 1's
// "pre-accepted" one (both vbal 0). A committed reply decides (sub-case 1); the parent takes the
// last reply of the highest vbal (1's), sees the leader's reply, runs Phase 1 again and commits
// deps[4] = 0.
func TestRecoveryCommittedReplyWins(t *testing.T) {
	c := newCluster(t, 5)
	c.propose(4, put(1, "z"))
	c.drop(instOf(4, 0))
	c.r[0].Alive[4] = false
	c.propose(0, put(1, "a"))
	c.run(kind("PreAccept"), from(0))
	c.run(kind("PreAcceptReply"), to(0))
	if !committed(c.inst(0, 0, 0)) {
		t.Fatalf("setup: 0 did not fast-commit 0.0: %s", instString(c.inst(0, 0, 0)))
	}
	c.drop(kind("Commit"))

	c.recover(4, 0, 0)
	c.run(kind("Prepare"), from(4), toAny(0, 1))
	c.drop(kind("Prepare"))
	c.r[4].Alive[0] = false
	c.run(kind("PrepareReply"), from(0))
	c.run(kind("PrepareReply"), from(1))
	c.settle(not(toAny(0)), not(fromAny(0)))
	if !committed(c.inst(4, 0, 0)) {
		t.Fatalf("replica 4 did not commit 0.0: %s", instString(c.inst(4, 0, 0)))
	}
	if e := c.agreementError(); e != "" {
		t.Fatal(e)
	}
}

// TestRecoveryIdenticalPreAcceptsOnlyAtDefaultBallot: 1 commits 1.0 (PUT k1) with 2 and 0 (its
// connections to 3 and 4 are down); 0 then proposes 0.0 (PUT k1, deps[1] = 0), which 2
// pre-accepts. Replica 3 recovers 0.0 with {3, 4, 0}: the leader replied, so Phase 1 again at
// 3's ballot b, reaching only 4, which pre-accepts deps[1] = -1 (it does not know 1.0). Replica
// 2 recovers 0.0 (its second try, ballot 12) with {2, 4, 1}: the highest vbal is b, not the default ballot, with one
// pre-accepted reply: sub-case 5 (Phase 1). The parent counts every pre-accepted reply (2's own
// at vbal 0 too: 2 >= floor(N/2)), compares only those at b (one), takes sub-case 3, accepts 4's
// attributes and commits deps[1] = -1: 0.0 and 1.0 interfere, neither is in the other's deps.
func TestRecoveryIdenticalPreAcceptsOnlyAtDefaultBallot(t *testing.T) {
	c := newCluster(t, 5)
	c.r[1].Alive[3], c.r[1].Alive[4] = false, false
	c.propose(1, put(1, "z"))
	c.settle(instOf(1, 0), among(0, 1, 2))
	if !committed(c.inst(1, 1, 0)) {
		t.Fatalf("setup: 1 did not commit 1.0: %s", instString(c.inst(1, 1, 0)))
	}
	c.drop(instOf(1, 0))

	c.propose(0, put(1, "a"))
	c.run(kind("PreAccept"), from(0), to(2))
	c.drop(instOf(0, 0))

	c.recover(3, 0, 0)
	c.run(kind("Prepare"), from(3), toAny(4, 0))
	c.drop(kind("Prepare"))
	c.run(kind("PrepareReply"), to(3))
	c.run(kind("PreAccept"), from(3), to(4))
	c.drop(instOf(0, 0))
	if s := c.inst(4, 0, 0).Status; s != PREACCEPTED && s != PREACCEPTED_EQ {
		t.Fatalf("setup: 4 did not pre-accept 0.0: %s", instString(c.inst(4, 0, 0)))
	}

	c.recover(2, 0, 0) // ballot 7, below 4's promise: lost
	c.drop(kind("Prepare"))
	c.recover(2, 0, 0) // ballot 12
	c.run(kind("Prepare"), from(2), toAny(4, 1))
	c.drop(kind("Prepare"))
	c.run(kind("PrepareReply"), to(2))
	c.settle(instOf(0, 0), not(toAny(0)), not(fromAny(0)))
	if !committed(c.inst(2, 0, 0)) {
		t.Fatalf("replica 2 did not commit 0.0: %s", instString(c.inst(2, 0, 0)))
	}
	if e := c.agreementError(); e != "" {
		t.Fatal(e)
	}
	if e := c.depsError(); e != "" {
		t.Fatal(e)
	}
}
