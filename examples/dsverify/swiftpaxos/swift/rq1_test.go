package swift

import (
	"math"
	"testing"

	"github.com/imdea-software/swiftpaxos/replica"
)

// R-Q1: ballots are int32 and every recovery raises the ballot (run's
// recover case: NextBallotOf adds up to 2N-1). The master may call
// BeTheLeader any number of times, so the ballot reached MaxInt32 and
// wrapped negative; AQ and Leader then index with a negative value (a panic).
// The recover case now refuses a recovery whose ballot would exceed
// replica.MaxBallot: from a ballot near MaxInt32, every recovery's ballot is
// one of this replica's in [0, MaxBallot] or the recovery is refused; far
// from the limit, a recovery proceeds.
func TestIssueRQ1_BallotDoesNotWrap(t *testing.T) {
	for _, n := range []int{3, 5} {
		for id := int32(0); id < int32(n); id++ {
			start := int32(math.MaxInt32 - 3*n)
			start -= start % int32(n) // a ballot of replica 0
			r := newTestReplica(t, n, id, start, false)
			refused := false
			for i := 0; i < 5 && !refused; i++ {
				func() {
					defer func() {
						if p := recover(); p != nil {
							t.Fatalf("N %d, replica %d, from ballot %d: panic: %v", n, id, r.ballot, p)
						}
					}()
					b, ok := r.recoveryBallot(-1)
					if !ok {
						refused = true
						if b != r.ballot {
							t.Fatalf("refused recovery changed the ballot %d to %d", r.ballot, b)
						}
						return
					}
					if b <= r.ballot || b > replica.MaxBallot(n) || replica.Leader(b, n) != id {
						t.Fatalf("N %d, replica %d: recovery from ballot %d takes ballot %d", n, id, r.ballot, b)
					}
					r.ballot = b // what handleNewLeader does
				}()
			}
			if !refused {
				t.Fatalf("N %d, replica %d: no refusal near MaxInt32 (ballot %d)", n, id, r.ballot)
			}
		}
	}
	// progress: far from the limit, a recovery proceeds
	r := newTestReplica(t, 3, 1, 0, false)
	if b, ok := r.recoveryBallot(-1); !ok || b != 4 {
		t.Fatalf("recovery from ballot 0 of replica 1: %d %v, want 4 true", b, ok)
	}
}
