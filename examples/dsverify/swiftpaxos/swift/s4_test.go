package swift

import (
	"testing"
	"time"
)

// S4: data races between the run loop and the descriptors' goroutines (Go's
// memory model; run with -race: go test -race -run TestIssueS4 ./swift/).
//
// A follower (replica 1 of three, ballot 0) is proposed commands as run's
// propose case does and gets the leader's fast acks; each command's
// descriptor has a goroutine (MaxDescRoutines = 100), which commits and
// executes the command, takes its history slot from the reply channel and
// ends (routineCount), while the run loop creates the next descriptors
// (routineCount). Then a new leader's MNewLeader arrives (handleNewLeader
// writes ballot and status while descriptors' goroutines may read them) and
// its MSync ends the recovery.
func TestIssueS4_RunLoopAndDescriptors(t *testing.T) {
	old := MaxDescRoutines
	MaxDescRoutines = 100
	defer func() { MaxDescRoutines = old }()

	r := withCs(newTestReplica(t, 3, 1, 0, true))
	for i := int32(0); i < 50; i++ {
		c := cid(1+i%3, i)
		if i%2 == 0 {
			propose(r, put(c, int64(i%2), "v"))
		} else {
			propose(r, get(c, int64(i%2)))
		}
		// the leader's fast ack: the descriptor's goroutine reads the ballot
		r.getCmdDesc(c, &MFastAck{Replica: 0, Ballot: 0, CmdId: c, Dep: []CommandId{},
			Checksum: []SHash{{}}}, nil)
	}
	// the leader: a descriptor created by an ack before the proposal has a
	// goroutine of its own, which proposes the command (seqnum)
	l := newTestReplica(t, 3, 0, 0, false)
	for i := int32(0); i < 20; i++ {
		c := cid(1+i%3, i)
		l.getCmdDesc(c, &MLightSlowAck{Replica: 2, Ballot: 0, CmdId: c}, nil)
		propose(l, put(c, int64(i%2), "v"))
	}

	done := make(chan struct{})
	go func() {
		r.handleNewLeader(&MNewLeader{Replica: 2, Ballot: 4})
		close(done)
	}()
	time.Sleep(50 * time.Millisecond)
	r.cs.syncChan <- &MSync{Replica: 2, Ballot: 4, Phases: map[CommandId]int{},
		Cmds: nil, Deps: nil}
	select {
	case <-done:
	case <-time.After(10 * time.Second):
		t.Fatal("recovery did not end")
	}
}
