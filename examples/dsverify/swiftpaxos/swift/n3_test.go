package swift

import (
	"io"
	"log"
	"os"
	"runtime"
	"testing"

	"github.com/imdea-software/swiftpaxos/state"
)

// N3 (stage 1 review, R1): a replica reports to a new leader every command it
// accepted or committed. handleSync gives each MSync command to a fresh
// descriptor goroutine (desc.msgs) and sends the new ballot's slow acks at
// once; if a higher MNewLeader is queued, stopDescs can stop a goroutine
// before it took its syncEntry, and fillNewLeaderAckN then reported the
// command in phase START with no dependencies (no recovery rule keeps it): a
// decided command could be lost.
//
// Replica 2 of three (ballot 1's follower, non-sequential descriptors) takes
// MSync(1) with twenty puts on one key, then its descriptors are stopped
// (the next MNewLeader's stopDescs) before any of them ran: GOMAXPROCS 1 and
// nothing in handleSync blocks, so each goroutine starts with both its stop
// and its syncEntry ready and Go's select takes either. Every command must
// be reported COMMIT with the MSync's dependencies. (Before the fix the test
// passed only if all twenty took the syncEntry: probability 2^-20.)
func TestIssueN3_SyncCommandsReported(t *testing.T) {
	defer runtime.GOMAXPROCS(runtime.GOMAXPROCS(1))
	old := MaxDescRoutines
	MaxDescRoutines = 100
	defer func() { MaxDescRoutines = old }()
	log.SetOutput(io.Discard)
	defer log.SetOutput(os.Stderr)

	r := newTestReplica(t, 3, 2, 1, false)
	r.status = RECOVERING // MNewLeader(1) handled: descriptors stopped
	const n = 20
	msg := &MSync{Replica: 1, Ballot: 1, Phases: map[CommandId]int{},
		Cmds: map[CommandId]state.Command{}, Deps: map[CommandId]Dep{}}
	prev := Dep{}
	for i := int32(0); i < n; i++ {
		c := cid(1, i)
		msg.Phases[c] = COMMIT
		msg.Cmds[c] = put(c, 7, "v").Command
		msg.Deps[c] = prev
		prev = Dep{c}
	}

	r.handleSync(msg)
	r.stopDescs()
	r.repchan.stop()

	m := &MNewLeaderAckN{}
	r.fillNewLeaderAckN(m)
	for c := range msg.Phases {
		phase, _, dep, ok := reported(m, c)
		if !ok || phase != COMMIT || !dep.Equals(msg.Deps[c]) {
			t.Fatalf("MSync command %v reported %v, phase %d, dependencies %v; want COMMIT with %v",
				c, ok, phase, dep, msg.Deps[c])
		}
	}
}
