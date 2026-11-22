//go:build amd64 || arm64

package concatlen

import (
	"slices"
	"testing"
	"unsafe"
)

func TestBoundary(t *testing.T) {
	big := make([]struct{}, 1<<62)
	if n := len(slices.Concat(big, big[:1<<62-1])); n != 1<<63-1 {
		t.Fatalf("len %d", n)
	}
	expectLenPanic(t, func() { _ = slices.Concat(big, big) })
}

func TestStringsOverflow(t *testing.T) {
	var x string
	// a []string of length 2^59 (never read: Concat panics while summing the lengths)
	s := unsafe.Slice(&x, 1<<59)
	ss := make([][]string, 16)
	for i := range ss {
		ss[i] = s
	}
	expectLenPanic(t, func() { _ = slices.Concat(ss...) })
}
