package state

import (
	"encoding/binary"
	"fmt"
	"math"
	"math/rand"
	"testing"
)

// formatUint10 (formatint.go) is fmt.Sprint(u) for a uint64.
func TestFixFormatUint10(t *testing.T) {
	xs := []uint64{0, 1, 9, 10, 11, 99, 100, 101, math.MaxUint32, math.MaxInt64, math.MaxUint64, math.MaxUint64 - 1}
	for s := 0; s < 64; s++ {
		p := uint64(1) << s
		xs = append(xs, p, p-1, p+1)
	}
	for p := uint64(1); p < math.MaxUint64/10; p *= 10 {
		xs = append(xs, p, p-1, p+1, 10*p-1)
	}
	rng := rand.New(rand.NewSource(5))
	for n := 0; n < 100000; n++ {
		xs = append(xs, rng.Uint64(), rng.Uint64()>>uint(rng.Intn(64)))
	}
	for _, x := range xs {
		if got, want := formatUint10(x), fmt.Sprint(x); got != want {
			t.Fatalf("formatUint10(%d) = %q, fmt.Sprint = %q", x, got, want)
		}
	}
	// Command.String's SCAN branch, its caller
	for _, n := range []uint64{0, 1, 12345, math.MaxUint64} {
		v := make([]byte, 8)
		binary.LittleEndian.PutUint64(v, n)
		c := Command{Op: SCAN, K: 5, V: v}
		if got, want := c.String(), "SCAN( 5 , "+fmt.Sprint(n)+" )"; got != want {
			t.Fatalf("String() = %q, want %q", got, want)
		}
	}
}
