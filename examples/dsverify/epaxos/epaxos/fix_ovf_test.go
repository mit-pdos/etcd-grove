package epaxos

import (
	"math"
	"testing"
)

// TestRecoveryBallotDoesNotOverflow: replica 3 has seen ballot MaxInt32 - 2 for 1.0 (after
// about 2^31/5 recoveries; time is not modeled, so unboundedly many are reachable). A new
// ballot must exceed every ballot seen; the next ballot owned by 3 does not fit an int32, so no
// recovery may start. On the parent the ballot wraps around to a negative ballot.
func TestRecoveryBallotDoesNotOverflow(t *testing.T) {
	c := newCluster(t, 5)
	r := c.r[3]
	in := r.newInstanceDefault(1, 0)
	in.bal = math.MaxInt32 - 2
	r.InstanceSpace[1][0] = in
	r.crtInstance[1] = 0
	c.recover(3, 1, 0)
	if in.lb != nil && in.lb.lastTriedBallot <= in.bal || r.InstanceSpace[1][0].bal < math.MaxInt32-2 {
		t.Fatalf("replica 3 recovers 1.0 at ballot %d after seeing %d", in.lb.lastTriedBallot, int32(math.MaxInt32-2))
	}
	if n := c.count(kind("Prepare")); n != 0 {
		t.Fatalf("replica 3 sent %d Prepares", n)
	}
}
