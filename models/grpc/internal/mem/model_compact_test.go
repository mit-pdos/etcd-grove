package mem

import (
	"math/rand"
	"slices"
	"testing"
)

// TestCompactExponentsIsCompact checks the model's compactExponents against slices.Compact
// (MODEL: buffer_pool.go): on random []uint8 inputs, sorted and unsorted, of lengths 0 to 40 and
// with small and full-range values, both return the same length and elements, and leave the
// input's array (capacity included) the same.
func TestCompactExponentsIsCompact(t *testing.T) {
	r := rand.New(rand.NewSource(1))
	for iter := 0; iter < 200000; iter++ {
		n := r.Intn(41)
		c := n + r.Intn(4)
		span := []int{1, 2, 4, 8, 64, 256}[r.Intn(6)]
		a := make([]uint8, c)
		for i := range a {
			a[i] = uint8(r.Intn(span))
		}
		if r.Intn(2) == 0 {
			slices.Sort(a[:n])
		}
		b := make([]uint8, c)
		copy(b, a)
		got := compactExponents(a[:n])
		want := slices.Compact(b[:n])
		if len(got) != len(want) || cap(got) != cap(want) || !slices.Equal(got, want) {
			t.Fatalf("input %v: compactExponents = %v (cap %d), slices.Compact = %v (cap %d)",
				b[:n], got, cap(got), want, cap(want))
		}
		if !slices.Equal(a, b) {
			t.Fatalf("arrays differ after compaction: model %v, slices.Compact %v", a, b)
		}
	}
}
