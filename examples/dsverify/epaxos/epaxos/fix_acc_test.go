package epaxos

import "testing"

// TestAcceptRecordsCommandAndStatus: replica 0 commits 0.0 (a PUT) on the slow path with
// acceptors 3 and 4, which never pre-accepted it (0's connections to its pre-acceptors 1 and 2
// broke before its Accepts). Replica 3 recovers 0.0 with the quorum {3, 1, 4}. The acceptors of
// the Accept must hold the command with status ACCEPTED (EPaxos Accept carries the command); on
// the parent they hold the attributes with status NONE and no command, the recovery sees no
// accepted reply at the highest vbal and commits a no-op over the committed PUT.
func TestAcceptRecordsCommandAndStatus(t *testing.T) {
	c := newCluster(t, 5)
	// 4.0 interferes with 0.0 and only replica 1 knows it: 0.0's pre-accept replies differ
	c.propose(4, put(1, "z"))
	c.run(kind("PreAccept"), from(4), to(1))
	c.drop(kind("PreAccept"), from(4))
	c.drop(kind("PreAcceptReply"), to(4))

	c.propose(0, put(1, "a"))
	c.run(kind("PreAccept"), from(0), toAny(1, 2))
	c.drop(kind("PreAccept"), from(0))
	reps := c.take(kind("PreAcceptReply"), to(0))
	c.r[0].Alive[1], c.r[0].Alive[2] = false, false
	for _, m := range reps {
		c.deliver(m)
	}
	if c.inst(0, 0, 0).Status != ACCEPTED {
		t.Fatalf("setup: 0.0 is not on the slow path at 0: %s", instString(c.inst(0, 0, 0)))
	}
	c.run(kind("Accept"), from(0), toAny(3, 4))
	c.run(kind("AcceptReply"), to(0))
	if !committed(c.inst(0, 0, 0)) {
		t.Fatalf("setup: 0 did not commit 0.0: %s", instString(c.inst(0, 0, 0)))
	}
	c.drop(kind("Commit"))
	for _, a := range []int32{3, 4} {
		in := c.inst(a, 0, 0)
		if in.Status != ACCEPTED || !sameCmds(in.Cmds, c.inst(0, 0, 0).Cmds) {
			t.Errorf("acceptor %d after the Accept: %s", a, instString(in))
		}
	}

	c.r[3].Alive[0] = false
	c.recover(3, 0, 0)
	c.run(kind("Prepare"), toAny(1, 4))
	c.drop(kind("Prepare"))
	c.run(kind("PrepareReply"), from(1))
	c.run(kind("PrepareReply"), from(4))
	c.settle(not(toAny(0)), not(fromAny(0)))
	if e := c.agreementError(); e != "" {
		t.Fatal(e)
	}
	if !committed(c.inst(3, 0, 0)) {
		t.Fatalf("replica 3 did not commit 0.0: %s", instString(c.inst(3, 0, 0)))
	}
}
