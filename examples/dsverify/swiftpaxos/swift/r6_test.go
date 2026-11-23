package swift

import (
	"sync"
	"testing"
	"time"

	"github.com/imdea-software/swiftpaxos/replica/defs"
)

// R6 (the race): BeTheLeader runs in an rpc goroutine and reads the ballot
// (r.leader()) while the run loop writes it (handleNewLeader, handleSync).
// Run with -race: go test -race -run TestIssueR6 ./swift/.
func TestIssueR6_BeTheLeaderReadsBallot(t *testing.T) {
	r := withCs(newTestReplica(t, 3, 1, 0, true))
	var wg sync.WaitGroup
	wg.Add(2)
	go func() { // the run loop
		defer wg.Done()
		r.handleNewLeader(&MNewLeader{Replica: 2, Ballot: 5})
	}()
	go func() { // the rpc server
		defer wg.Done()
		r.BeTheLeader(&defs.BeTheLeaderArgs{}, defs.NewBeTheLeaderReply())
	}()
	time.Sleep(50 * time.Millisecond)
	r.cs.syncChan <- &MSync{Replica: 2, Ballot: 5, Phases: map[CommandId]int{}}
	wg.Wait()
}
