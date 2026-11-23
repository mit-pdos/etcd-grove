package swift

import (
	"testing"
	"time"

	"github.com/imdea-software/swiftpaxos/replica"
)

// F1: run's recover case searches for a ballot of this replica whose fast quorum is alive. When
// no peer is alive (their connections broke: Alive is false), the search never ended: each round
// adds N to the int32 ballot, which wraps negative, and QuorumSet.AQ then divides by zero.
func TestIssueF1_NoAliveQuorumTerminates(t *testing.T) {
	r := newTestReplica(t, 3, 1, 0, true)
	qs, err := replica.NewQuorumSystem(2, r.Replica, "")
	if err != nil {
		t.Fatal(err)
	}
	r.qs = qs
	r.fixedMajority = true
	for i := range r.Alive {
		r.Alive[i] = i == int(r.Id)
	}
	done := make(chan int32, 1)
	go func() {
		defer func() {
			if p := recover(); p != nil {
				t.Errorf("panic: %v", p)
				done <- -1
			}
		}()
		b, _ := r.aliveQuorumBallot(replica.NextBallotOf(r.Id, 0, r.N))
		done <- b
	}()
	select {
	case b := <-done:
		if b < 0 || replica.Leader(b, r.N) != r.Id {
			t.Fatalf("ballot %d: not one of replica %d's", b, r.Id)
		}
	case <-time.After(20 * time.Second):
		t.Fatal("the search for an alive fast quorum does not end")
	}
}
