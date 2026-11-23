package epaxos

import "testing"

// TestBatchDepsCoverEveryCommand: replica 1 commits 1.0 (PUT k1) and then 1.1 (PUT k2) with the
// replicas other than 0 (its connection to 0 is down). Replica 0 then proposes one batch [PUT k1,
// PUT k2]. The deps in row 1 must cover 1.1 (the batch's PUT k2 interferes with it); each acceptor
// of the parent stops at the batch's first command that raises deps[1] (k1: 1.0) and 0.0 commits
// with deps[1] = 0: 0.0 and 1.1 interfere, neither is in the other's deps.
func TestBatchDepsCoverEveryCommand(t *testing.T) {
	c := newCluster(t, 5)
	c.r[1].Alive[0] = false
	c.propose(1, put(1, "a"))
	c.settle(not(toAny(0)), not(fromAny(0)))
	c.propose(1, put(2, "b"))
	c.settle(not(toAny(0)), not(fromAny(0)))
	c.drop(to(0))
	c.r[1].Alive[0] = true
	c.propose(0, put(1, "c"), put(2, "d"))
	c.settle()
	for i := int32(1); i < 5; i++ {
		for _, k := range []int32{0, 1} {
			if !committed(c.inst(i, 1, k)) || !committed(c.inst(i, 0, 0)) {
				t.Fatalf("setup: replica %d did not commit everything", i)
			}
		}
	}
	if e := c.agreementError(); e != "" {
		t.Fatal(e)
	}
	if e := c.depsError(); e != "" {
		t.Fatal(e)
	}
}
