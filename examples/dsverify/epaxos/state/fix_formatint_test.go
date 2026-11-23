package state

import (
	"math"
	"math/rand"
	"strconv"
	"testing"
)

// formatInt16 (formatint.go) is strconv.FormatInt(., 16).
func TestFixFormatInt16(t *testing.T) {
	xs := []int64{0, 1, -1, 9, 10, 15, 16, -15, -16, -17, 255, 256, -255, -256,
		math.MaxInt32, math.MinInt32, math.MaxInt64, math.MinInt64, math.MaxInt64 - 1, math.MinInt64 + 1}
	for s := 0; s < 63; s++ {
		p := int64(1) << s
		xs = append(xs, p, p-1, p+1, -p, -p-1, -p+1)
	}
	rng := rand.New(rand.NewSource(4))
	for n := 0; n < 100000; n++ {
		xs = append(xs, int64(rng.Uint64()), rng.Int63()>>uint(rng.Intn(63))*int64(1-2*rng.Intn(2)))
	}
	for _, x := range xs {
		if got, want := formatInt16(x), strconv.FormatInt(x, 16); got != want {
			t.Fatalf("formatInt16(%d) = %q, strconv.FormatInt = %q", x, got, want)
		}
	}
	// Key.String, its caller
	for _, k := range []Key{0, 1, -1, 0xff, math.MaxInt64, math.MinInt64} {
		if got, want := k.String(), strconv.FormatInt(int64(k), 16); got != want {
			t.Fatalf("Key(%d).String() = %q, want %q", int64(k), got, want)
		}
	}
}
