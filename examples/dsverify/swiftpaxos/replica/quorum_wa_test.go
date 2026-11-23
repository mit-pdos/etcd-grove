package replica

import "testing"

// Verification workaround: subsets deletes through the underlying map type
// (delete(map[int32]struct{}(q), ...)); the quorum sets are as before: each
// leader's quorums are exactly the quorumSize-subsets containing it.
func TestQuorumSetSubsets(t *testing.T) {
	binom := func(n, k int) int {
		r := 1
		for i := 0; i < k; i++ {
			r = r * (n - i) / (i + 1)
		}
		return r
	}
	for _, n := range []int{3, 5} {
		size := n/2 + 1
		qs := NewQuorumSet(size, n)
		for l := int32(0); l < int32(n); l++ {
			if got, want := len(qs[l]), binom(n-1, size-1); got != want {
				t.Fatalf("N %d leader %d: %d quorums, want %d", n, l, got, want)
			}
			for i, q := range qs[l] {
				if _, ok := q[l]; !ok || len(q) != size {
					t.Fatalf("N %d leader %d quorum %d: %v", n, l, i, q)
				}
				for j := int32(0); j < i; j++ {
					if q.Equals(qs[l][j]) {
						t.Fatalf("N %d leader %d: quorum %v twice", n, l, q)
					}
				}
			}
		}
	}
}
