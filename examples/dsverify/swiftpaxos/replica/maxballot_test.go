package replica

import (
	"math"
	"testing"
)

// The MaxInt32 literal in MaxBallot (verification workaround) equals math.MaxInt32.
func TestMaxBallotLiteral(t *testing.T) {
	for n := 1; n <= 16; n++ {
		if MaxBallot(n) != int32(math.MaxInt32)-2*int32(n) {
			t.Fatalf("MaxBallot(%d) = %d", n, MaxBallot(n))
		}
	}
}
