package epaxos

import "testing"

// TestAcceptRejectionIsNotAVote: replica 3 recovers 0.0 (whose PreAccepts were lost) at ballot
// b1: sub-case 6, Phase 1 for a no-op with 4 and 2, Accept(b1) to 4 and 1; 4 accepts (its reply
// is lost), the Accept to 1 is delayed. 3 recovers again at b2 with {3, 4, 1}: accepted at b1,
// sub-case 2, Accept(b2). The delayed Accept(b1) then reaches 1, which has promised b2 and
// rejects it, answering with its ballot b2. A proposer counts only acceptances of its own Accept:
// the parent counts 1's rejection as a vote at b2 and, with 4's, commits the no-op with only 3
// and 4 having voted at b2. Its Commits are lost; 1 then learns its own 1.0 (PUT k0, which
// interferes with the no-op's key 0), and 2 recovers 0.0 with {2, 0, 1}: highest vote the
// pre-accepted no-op at b1, Phase 1 with new attributes (deps[1] = 0): different deps for 0.0.
func TestAcceptRejectionIsNotAVote(t *testing.T) {
	c := newCluster(t, 5)
	c.propose(0, put(1, "a"))
	c.drop(instOf(0, 0))

	for q := int32(0); q < 5; q++ {
		c.r[3].Alive[q] = q != 3 && q != 0
	}
	c.recover(3, 0, 0) // b1
	c.run(kind("Prepare"), from(3), toAny(4, 1))
	c.drop(kind("Prepare"))
	c.run(kind("PrepareReply"), to(3))
	c.run(kind("PreAccept"), from(3), toAny(4, 2))
	c.drop(kind("PreAccept"))
	c.run(kind("PreAcceptReply"), to(3))
	if c.inst(3, 0, 0).Status != ACCEPTED {
		t.Fatalf("setup: 3 is not accepting 0.0 at b1: %s", instString(c.inst(3, 0, 0)))
	}
	c.run(kind("Accept"), from(3), to(4))
	c.drop(kind("AcceptReply"))
	late := c.take(kind("Accept"), from(3), to(1))

	c.recover(3, 0, 0) // b2
	c.run(kind("Prepare"), from(3), toAny(4, 1))
	c.drop(kind("Prepare"))
	c.run(kind("PrepareReply"), to(3))
	if c.inst(3, 0, 0).Status != ACCEPTED || c.count(kind("Accept"), from(3)) == 0 {
		t.Fatalf("setup: 3 is not accepting 0.0 at b2: %s", instString(c.inst(3, 0, 0)))
	}
	for _, m := range late {
		c.deliver(m)
	}
	c.run(kind("AcceptReply"), from(1), to(3))
	c.run(kind("Accept"), from(3), to(4))
	c.drop(kind("Accept"))
	c.run(kind("AcceptReply"), from(4), to(3))
	c.drop(kind("Commit"))

	c.propose(1, put(0, "z"))
	c.drop(instOf(1, 0))
	for q := int32(0); q < 5; q++ {
		c.r[2].Alive[q] = q == 0 || q == 1
	}
	c.recover(2, 0, 0) // below 1's promise: lost
	c.drop(kind("Prepare"))
	c.recover(2, 0, 0)
	c.settle(instOf(0, 0), among(0, 1, 2))
	if !committed(c.inst(2, 0, 0)) {
		t.Fatalf("2 did not commit 0.0: %s", instString(c.inst(2, 0, 0)))
	}
	if e := c.agreementError(); e != "" {
		t.Fatal(e)
	}
}
