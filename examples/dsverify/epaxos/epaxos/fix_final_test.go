package epaxos

import "testing"

// TestRecoveryDoesNotCopyExecuted: 0 commits 0.0 (PUT k1 "a") with acceptors 1 and 2 on the
// slow path (only 1 knew 4.0, a GET of k1); only 1 gets the Commit and executes it. Replica 3 recovers 0.0 with {3, 1, 4}: 1's reply is
// "executed" (sub-case 1). Replica 3 must commit 0.0 and then execute it itself: EXECUTED means
// executed by this replica. The parent copies the reply's status EXECUTED, so 3 never applies
// the PUT and its store differs from 1's.
func TestRecoveryDoesNotCopyExecuted(t *testing.T) {
	c := newCluster(t, 5)
	held := commitSlowAfter(t, c, get(1))
	commit4(t, c, held)
	c.r[0].bcastCommit(0, 0)
	c.run(kind("Commit"), to(1))
	c.drop(kind("Commit"))
	c.execAll(1)
	if c.inst(1, 0, 0).Status != EXECUTED {
		t.Fatalf("setup: 1 did not execute 0.0")
	}
	c.r[3].Alive[0] = false
	c.recover(3, 0, 0)
	c.run(kind("Prepare"), toAny(1, 4))
	c.drop(kind("Prepare"))
	c.run(kind("PrepareReply"))
	if s := c.inst(3, 0, 0).Status; s != COMMITTED {
		t.Errorf("replica 3 recovered 0.0 with status %d", s)
	}
	c.execAll(3)
	if v1, v3 := c.value(1, 1), c.value(3, 1); v1 != v3 {
		t.Fatalf("after executing 0.0, key 1 is %q at replica 1 and %q at replica 3", v1, v3)
	}
}

// TestCommittedInstanceStaysCommitted: a replica's committed (and executed) instance is final.
// (b) Replica 0's AcceptReplies for 0.0 are delayed while a recovery by 3 commits 0.0 and 0
// executes it; the late replies make the parent set 0.0 back to COMMITTED. (c) The same with
// 0's PreAcceptReplies: the late replies make the parent fast-commit 0.0 again over its
// executed copy. An executed instance set back to COMMITTED is executable again.
func TestCommittedInstanceStaysCommitted(t *testing.T) {
	// (b)
	c := newCluster(t, 5)
	c.propose(4, put(1, "z"))
	c.run(kind("PreAccept"), from(4), to(1))
	held := c.take(instOf(4, 0))
	c.propose(0, put(1, "a"))
	c.run(kind("PreAccept"), from(0), toAny(1, 2))
	c.drop(kind("PreAccept"), from(0))
	c.run(kind("PreAcceptReply"), to(0))
	c.run(kind("Accept"), from(0), toAny(1, 2))
	c.drop(kind("Accept"), from(0))
	late := c.take(kind("AcceptReply"), to(0))
	c.r[3].Alive[0] = false
	c.recover(3, 0, 0)
	c.drop(kind("Prepare"), to(4))
	c.settle(not(toAny(0)), not(fromAny(0)))
	if !committed(c.inst(3, 0, 0)) {
		t.Fatalf("setup (b): 3 did not commit 0.0: %s", instString(c.inst(3, 0, 0)))
	}
	commit4(t, c, held)
	c.r[3].Alive[0] = true
	c.r[3].bcastCommit(0, 0)
	c.run(kind("Commit"), to(0))
	c.execAll(0)
	if c.inst(0, 0, 0).Status != EXECUTED {
		t.Fatalf("setup (b): 0 did not execute 0.0: %s", instString(c.inst(0, 0, 0)))
	}
	for _, m := range late {
		c.deliver(m)
	}
	if s := c.inst(0, 0, 0).Status; s != EXECUTED {
		t.Errorf("(b) replica 0's executed 0.0 now has status %d", s)
	}

	// (c)
	c = newCluster(t, 5)
	c.propose(0, put(1, "a"))
	c.run(kind("PreAccept"), from(0))
	late = c.take(kind("PreAcceptReply"), to(0))
	c.r[3].Alive[0] = false
	c.recover(3, 0, 0)
	c.drop(kind("Prepare"), toAny(0, 4))
	c.settle(not(toAny(0)), not(fromAny(0)))
	if !committed(c.inst(3, 0, 0)) {
		t.Fatalf("setup (c): 3 did not commit 0.0: %s", instString(c.inst(3, 0, 0)))
	}
	c.r[3].Alive[0] = true
	c.r[3].bcastCommit(0, 0)
	c.run(kind("Commit"), to(0))
	c.execAll(0)
	if c.inst(0, 0, 0).Status != EXECUTED {
		t.Fatalf("setup (c): 0 did not execute 0.0: %s", instString(c.inst(0, 0, 0)))
	}
	for _, m := range late {
		c.deliver(m)
	}
	if s := c.inst(0, 0, 0).Status; s != EXECUTED {
		t.Errorf("(c) replica 0's executed 0.0 now has status %d", s)
	}
}
