package master

import (
	"math"
	"testing"
)

// maxFloat64 (master.go) is math.MaxFloat64: the same float64 (bit for bit), and so the same
// comparisons in Register's choice of the leader.
func TestFixMaxFloat64(t *testing.T) {
	var a, b float64 = maxFloat64, math.MaxFloat64
	if math.Float64bits(a) != math.Float64bits(b) {
		t.Fatalf("maxFloat64 %x, math.MaxFloat64 %x", math.Float64bits(a), math.Float64bits(b))
	}
	for _, x := range []float64{0, -1, 1, math.SmallestNonzeroFloat64, math.Nextafter(math.MaxFloat64, 0),
		math.MaxFloat64, math.Inf(1), math.Inf(-1), math.NaN(), 1e308, -math.MaxFloat64} {
		if (x < a) != (x < b) || (x == a) != (x == b) {
			t.Fatalf("comparison with %v differs", x)
		}
	}
}
