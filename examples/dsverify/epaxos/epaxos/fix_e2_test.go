package epaxos

import (
	"testing"
	"time"

	"github.com/imdea-software/swiftpaxos-epaxos/state"
)

// TestSCCOrderIsDeterministic: 0.0 (PUT k1 "x") and 0.1 (PUT k1 "y") are committed with equal
// seq and each in the other's deps (one strongly connected component). Replica 1 receives their
// Commits in the order 0.0, 0.1, replica 2 in the order 0.1, 0.0. Every replica must execute a
// component in the same order (EPaxos execution: by seq, ties broken by an order all replicas
// compute alike); the parent breaks ties by proposeTime, the local time at which each replica
// created its copy of the instance, and the two replicas end with different values of k1.
func TestSCCOrderIsDeterministic(t *testing.T) {
	c := newCluster(t, 5)
	deps0 := []int32{1, -1, -1, -1, -1}
	deps1 := []int32{0, -1, -1, -1, -1}
	c0 := &Commit{LeaderId: 0, Replica: 0, Instance: 0, Ballot: 0, Command: []state.Command{put(1, "x")}, Seq: 3, Deps: deps0}
	c1 := &Commit{LeaderId: 0, Replica: 0, Instance: 1, Ballot: 0, Command: []state.Command{put(1, "y")}, Seq: 3, Deps: deps1}
	c.r[1].handleCommit(c0)
	time.Sleep(time.Millisecond)
	c.r[1].handleCommit(c1)
	c.r[2].handleCommit(c1)
	time.Sleep(time.Millisecond)
	c.r[2].handleCommit(c0)
	c.execAll(1)
	c.execAll(2)
	for _, i := range []int32{1, 2} {
		for k := int32(0); k < 2; k++ {
			if c.inst(i, 0, k).Status != EXECUTED {
				t.Fatalf("replica %d did not execute 0.%d", i, k)
			}
		}
	}
	if v1, v2 := c.value(1, 1), c.value(2, 1); v1 != v2 {
		t.Fatalf("after executing 0.0 and 0.1, k1 is %q at replica 1 and %q at replica 2", v1, v2)
	}
}
