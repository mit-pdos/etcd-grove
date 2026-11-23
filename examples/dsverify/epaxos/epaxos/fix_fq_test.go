package epaxos

import "testing"

// TestFastPathNeedsRecoverableQuorum: replica 3 proposes 3.0 (PUT k1), which only 4 learns.
// Replica 0 proposes 0.0 (PUT k1); 1 and 2 pre-accept it with identical attributes (deps[3] =
// -1). Replica 4 recovers 0.0 with {4, 3, 2}: one pre-accepted reply, sub-case 5, Phase 1 at 4's
// ballot (deps[3] = 0), committed with 1, 2 and 3. The simplified recovery is sound only with the
// fast quorum of 2F replicas (here 4: the leader and 3 identical replies), which any prepare
// quorum without the leader intersects in floor(N/2) replicas; the parent fast-commits on
// F + floor((F+1)/2) = 3 (two identical replies) and commits deps[3] = -1 at 0.
func TestFastPathNeedsRecoverableQuorum(t *testing.T) {
	c := newCluster(t, 5)
	c.propose(3, put(1, "z"))
	c.run(kind("PreAccept"), from(3), to(4))
	c.drop(instOf(3, 0))

	c.propose(0, put(1, "a"))
	c.run(kind("PreAccept"), from(0), toAny(1, 2))
	held := c.take(kind("PreAccept"), from(0)) // delayed
	c.run(kind("PreAcceptReply"), to(0))

	c.r[4].Alive[0] = false
	c.recover(4, 0, 0)
	c.run(kind("Prepare"), from(4), toAny(3, 2))
	c.drop(kind("Prepare"))
	c.run(kind("PrepareReply"), to(4))
	c.settle(not(toAny(0)), not(fromAny(0)))
	if !committed(c.inst(4, 0, 0)) {
		t.Fatalf("replica 4 did not commit 0.0: %s", instString(c.inst(4, 0, 0)))
	}
	for _, m := range held {
		c.deliver(m)
	}
	c.settle()
	if e := c.agreementError(); e != "" {
		t.Fatal(e)
	}
}

// TestSlowPathWhenAllPreAcceptsAnswered: 0's connections to 3 and 4 are down: its thrifty
// PreAccept reaches 1 and 2 only; their identical replies are all it can get, and 0 must commit
// (on the slow path), not wait for a third reply.
func TestSlowPathWhenAllPreAcceptsAnswered(t *testing.T) {
	c := newCluster(t, 5)
	c.r[0].Alive[3], c.r[0].Alive[4] = false, false
	c.propose(0, put(1, "a"))
	c.settle()
	if !committed(c.inst(0, 0, 0)) {
		t.Fatalf("0 did not commit 0.0: %s", instString(c.inst(0, 0, 0)))
	}
}

// TestSlowPathOnDisagreement: two disagreeing replies (a majority with the leader) start the
// slow path at once, without waiting for the third reply.
func TestSlowPathOnDisagreement(t *testing.T) {
	c := newCluster(t, 5)
	c.propose(4, put(1, "z"))
	c.run(kind("PreAccept"), from(4), to(1))
	c.drop(instOf(4, 0))
	c.propose(0, put(1, "a"))
	c.run(kind("PreAccept"), from(0), toAny(1, 2))
	c.drop(kind("PreAccept"), from(0))
	c.run(kind("PreAcceptReply"), to(0))
	if s := c.inst(0, 0, 0).Status; s != ACCEPTED {
		t.Fatalf("0 has 0.0 with status %d after two disagreeing replies", s)
	}
}
