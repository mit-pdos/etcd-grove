package master

import (
	"math"
	"testing"
)

// The literal that replaced math.MaxFloat64 in Register (verification workaround) is the same value.
func TestMaxFloat64Literal(t *testing.T) {
	if x, y := float64(1.7976931348623157e308), float64(math.MaxFloat64); x != y {
		t.Fatal("literal differs from math.MaxFloat64")
	}
}
