package swift

import (
	"testing"
	"time"
)

// N1 (found here): a replica recovering for ballot 4 that gets the MNewLeader
// of a higher ballot (another BeTheLeader: the client node's, the master's)
// handles it inside the first recovery's loop; handleNewLeader stopped the
// reply channel again, and stop waits for the channel's goroutine, which had
// exited: the run loop blocked forever.
func TestIssueN1_NestedNewLeader(t *testing.T) {
	r := withCs(newTestReplica(t, 3, 1, 0, true))
	done := make(chan struct{})
	go func() {
		r.handleNewLeader(&MNewLeader{Replica: 2, Ballot: 5})
		close(done)
	}()
	r.cs.newLeaderChan <- &MNewLeader{Replica: 0, Ballot: 6}
	time.Sleep(100 * time.Millisecond) // the MNewLeader first
	r.cs.syncChan <- &MSync{Replica: 0, Ballot: 6, Phases: map[CommandId]int{}}
	select {
	case <-done:
	case <-time.After(5 * time.Second):
		t.Fatal("the run loop is blocked in the nested recovery")
	}
}
