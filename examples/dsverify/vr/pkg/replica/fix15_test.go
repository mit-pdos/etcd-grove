package replica

import (
	"fmt"
	"log/slog"
	"testing"

	"github.com/tangledbytes/go-vsr/pkg/events"
	"github.com/tangledbytes/go-vsr/pkg/ipv4port"
	"github.com/tangledbytes/go-vsr/pkg/log"
	vsrtime "github.com/tangledbytes/go-vsr/pkg/time"
)

// newCluster5 is newCluster with five replicas (f = 2) at 127.0.0.1:7101..7105. Events the
// replicas send are recorded by the harness's fakeNet (as replies: replicaAt knows only the
// three-replica addresses); this test drops them all.
func newCluster5(t *testing.T) *cluster {
	members := []string{"127.0.0.1:7101", "127.0.0.1:7102", "127.0.0.1:7103", "127.0.0.1:7104", "127.0.0.1:7105"}
	c := &cluster{t: t, clock: vsrtime.NewVirtual(1)}
	for i := range members {
		i := i
		var a ipv4port.IPv4Port
		if err := a.FromHostPort(members[i]); err != nil {
			t.Fatal(err)
		}
		c.addrs = append(c.addrs, a)
		c.executed = append(c.executed, nil)
		r, err := New(Config{
			HeartbeatTimeout: hb,
			SrvHandler: func(op string) string {
				c.executed[i] = append(c.executed[i], op)
				return "res " + op
			},
			Network: &fakeNet{c: c, id: i},
			Time:    c.clock,
			ID:      uint64(i),
			Members: members,
			Logger:  slog.New(slog.DiscardHandler),
		})
		if err != nil {
			t.Fatal(err)
		}
		c.reps = append(c.reps, r)
	}
	return c
}

// V15: VR §4.1 step 5: the primary commits op n after f PREPAREOKs from different backups for
// op n in the current view. With five replicas (f = 2) a pending entry can outlive its view
// holding the primary's own response and one backup's (2 < 3, not committed). When the same
// replica is primary again in a later view whose log is shorter, a different op takes that op
// number, and the stale entry's backup response was counted for it: one PREPAREOK of the new
// view committed an op only 2 of 5 replicas hold. Fixed by 8d51136 (finalizeViewChange starts
// from no pending PrepareOKs).
func TestFixV15StalePrepareOKDoesNotCommit(t *testing.T) {
	c := newCluster5(t)
	// View 0, primary 0: op 1 (client 1's request 1); replica 1 acknowledges it. Not committed.
	c.request(0, 1, 1)
	c.drop(func(m msg) bool { return true })
	c.replies = nil
	c.submit(0, c.addrs[1], events.EventPrepareOK, events.PrepareOK{ViewNum: 0, OpNum: 1, ReplicaID: 1})
	if len(c.executed[0]) != 0 {
		t.Fatalf("setup: op 1 of view 0 committed with 2 of 5: %q", c.executed[0])
	}
	// View 5 (primary 0 again) from the DOVIEWCHANGEs of replicas 2, 3 and 4 (which never got
	// op 1): the new log is empty.
	c.submit(0, c.addrs[2], events.EventStartViewChange, events.StartViewChange{ViewNum: 5, ReplicaID: 2})
	for _, i := range []int{2, 3, 4} {
		c.submit(0, c.addrs[i], events.EventDoViewChange, events.DoViewChange{
			ViewNum: 5, Logs: log.Logs{}, LastStableViewNum: 0, OpNum: 0, CommitNum: 0, ReplicaID: uint64(i),
		})
	}
	r := c.reps[0]
	if r.state.Status != ReplicaStatusNormal || r.state.ViewNumber != 5 || r.state.OpNum != 0 {
		t.Fatalf("setup: view 5 did not start at replica 0 with an empty log: %+v", r.state)
	}
	c.pending, c.replies = nil, nil
	// Op 1 of view 5 is client 2's request 1; one PREPAREOK of view 5 (replica 2) arrives.
	c.request(0, 2, 1)
	c.pending = nil
	c.submit(0, c.addrs[2], events.EventPrepareOK, events.PrepareOK{ViewNum: 5, OpNum: 1, ReplicaID: 2})
	if len(c.executed[0]) != 0 {
		t.Fatalf("V15 (VR §4.1 step 5: f PREPAREOKs from different backups for the op in the current view): primary 0 of view 5 executed %q with PREPAREOKs of view 5 from replicas {0, 2} only (2 of 5; replica 1's response was for op 1 of view 0, %s)",
			c.executed[0], fmt.Sprint(op(1, 1)))
	}
}
