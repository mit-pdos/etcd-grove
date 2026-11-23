package epaxos

import "testing"

func noPanic(t *testing.T, what string, f func()) {
	t.Helper()
	defer func() {
		if e := recover(); e != nil {
			t.Fatalf("%s panicked: %v", what, e)
		}
	}()
	f()
}

// TestProposeBeyondRowCapacity: replica 0's row is full (crtInstance = MAX_INSTANCE - 1, rows
// allocated as New does): a new proposal must not create an instance past the row's capacity;
// the parent indexes InstanceSpace[0][MAX_INSTANCE] and panics.
func TestProposeBeyondRowCapacity(t *testing.T) {
	c := newCluster(t, 5)
	r := c.r[0]
	r.InstanceSpace[0] = make([]*Instance, MAX_INSTANCE)
	r.crtInstance[0] = MAX_INSTANCE - 1
	noPanic(t, "handlePropose", func() { c.propose(0, put(1, "a")) })
	if r.crtInstance[0] != MAX_INSTANCE-1 || c.count() != 0 {
		t.Fatalf("an instance was created: crtInstance %d, %d messages", r.crtInstance[0], c.count())
	}
}

// TestLastInstanceOfRowCommits: replica 0 has instances up to MAX_INSTANCE - 2, all committed
// everywhere (CommittedUpTo = MAX_INSTANCE - 2). On the parent a new proposal creates instance
// MAX_INSTANCE - 1, which commits; updateCommitted then reads InstanceSpace[0][MAX_INSTANCE] and
// panics. The row's last slot must stay unused.
func TestLastInstanceOfRowCommits(t *testing.T) {
	c := newCluster(t, 5)
	for _, r := range c.r {
		r.InstanceSpace[0] = make([]*Instance, MAX_INSTANCE)
		r.crtInstance[0] = MAX_INSTANCE - 2
		r.CommittedUpTo[0] = MAX_INSTANCE - 2
	}
	noPanic(t, "proposing and committing", func() {
		c.propose(0, put(1, "a"))
		c.settle()
	})
}
