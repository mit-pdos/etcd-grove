package epaxos

import (
	"testing"

	"github.com/imdea-software/swiftpaxos-epaxos/state"
)

// commitSlow has replica 0 commit 0.0 (PUT k1 "a") on the slow path with acceptors 1 and 2 (1
// knows the interfering 4.0, so the pre-accept replies differ); its Commits are lost. It returns
// 4.0's held messages: commit4 has 4.0 committed everywhere.
func commitSlow(t *testing.T, c *tcluster) []*tmsg {
	return commitSlowAfter(t, c, put(1, "z"))
}

// commitSlowAfter is commitSlow with 4.0's command cmd4 (it must interfere with PUT k1).
func commitSlowAfter(t *testing.T, c *tcluster, cmd4 state.Command) []*tmsg {
	c.propose(4, cmd4)
	c.run(kind("PreAccept"), from(4), to(1))
	held := c.take(instOf(4, 0))
	c.propose(0, put(1, "a"))
	c.run(kind("PreAccept"), from(0), toAny(1, 2))
	c.drop(kind("PreAccept"), from(0))
	c.run(kind("PreAcceptReply"), to(0))
	c.run(kind("Accept"), from(0), toAny(1, 2))
	c.drop(kind("Accept"), from(0))
	c.run(kind("AcceptReply"), to(0))
	if !committed(c.inst(0, 0, 0)) {
		t.Fatalf("setup: 0 did not commit 0.0: %s", instString(c.inst(0, 0, 0)))
	}
	c.drop(kind("Commit"))
	return held
}

// commit4 delivers 4.0's held messages and every message about 4.0 until none is left.
func commit4(t *testing.T, c *tcluster, held []*tmsg) {
	for _, m := range held {
		c.deliver(m)
	}
	c.settle(instOf(4, 0))
	for i := int32(0); i < 5; i++ {
		if !committed(c.inst(i, 4, 0)) {
			t.Fatalf("setup: replica %d did not commit 4.0: %s", i, instString(c.inst(i, 4, 0)))
		}
	}
}

// TestPrepareQuorumCountsDistinctAcceptors: 0 commits 0.0 with acceptors 1 and 2. Replica 3
// recovers 0.0 twice (its executor asks again); replica 4 gets the second Prepare first, then
// the first one, and answers both with its current ballot, the second one's. A prepare quorum
// is a majority of distinct acceptors: the parent counts 4's two replies and decides with
// {3, 4, 4}, sees nothing, and commits a no-op over the committed PUT.
func TestPrepareQuorumCountsDistinctAcceptors(t *testing.T) {
	c := newCluster(t, 5)
	commitSlow(t, c)

	c.r[3].Alive[0] = false
	c.recover(3, 0, 0)
	first := c.take(kind("Prepare"), from(3))
	c.recover(3, 0, 0)
	c.run(kind("Prepare"), from(3), to(4))
	for _, m := range first {
		if m.to == 4 {
			c.deliver(m)
		}
	}
	c.run(kind("PrepareReply"), from(4))
	// 3's Phase 1 (if any): 4 answers first
	c.run(kind("PreAccept"), from(3), to(4))
	c.run(kind("PreAcceptReply"), from(4))
	c.settle(not(toAny(0)), not(fromAny(0)))
	if e := c.agreementError(); e != "" {
		t.Fatal(e)
	}
	if !committed(c.inst(3, 0, 0)) {
		t.Fatalf("replica 3 did not commit 0.0: %s", instString(c.inst(3, 0, 0)))
	}
}

// TestOnePrepareDecisionPerBallot: replica 3 recovers 1.0 twice (ballots b1 < b2) and decides
// at b2 with {3, 4, 0} (nothing known: Phase 1 for a no-op at b2). Then the late replies for b2
// of 1 (the leader: pre-accepted PUT) and 2 arrive, and 4 answers the delayed Prepare for b1
// with its ballot b2. Paxos proposes at most one value per ballot: the parent's Phase-1
// bookkeeping is still "preparing", collects these three replies as a new quorum for b2 and runs
// Phase 1 again at b2 for the PUT.
func TestOnePrepareDecisionPerBallot(t *testing.T) {
	c := newCluster(t, 5)
	c.propose(1, put(2, "a"))
	c.drop(kind("PreAccept"))
	c.recover(3, 1, 0)
	first := c.take(kind("Prepare"), from(3))
	c.recover(3, 1, 0)
	b2 := c.inst(3, 1, 0).lb.lastTriedBallot
	c.run(kind("Prepare"), from(3), toAny(4, 0))
	c.run(kind("PrepareReply"), to(3))
	in := c.inst(3, 1, 0)
	if in.lb.preparing && len(in.lb.prepareReplies) > 0 || in.bal != b2 || in.Status == NONE {
		t.Fatalf("setup: replica 3 has not decided at %d: %s", b2, instString(in))
	}
	cmds := in.Cmds
	c.run(kind("Prepare"), from(3), toAny(1, 2))
	for _, m := range first {
		if m.to == 4 {
			c.deliver(m)
		}
	}
	c.run(kind("PrepareReply"), to(3))
	in2 := c.inst(3, 1, 0)
	if in2 != in || !sameCmds(in2.Cmds, cmds) {
		t.Fatalf("replica 3 proposed twice at ballot %d: %s, then %s", b2, cmdsString(cmds), instString(in2))
	}
}
