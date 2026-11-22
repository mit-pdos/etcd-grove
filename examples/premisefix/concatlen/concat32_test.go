//go:build 386

package concatlen

import (
	"slices"
	"testing"
)

func TestStrings32(t *testing.T) {
	s := make([]string, 1<<16)
	ss := make([][]string, 1<<15)
	for i := range ss {
		ss[i] = s
	}
	expectLenPanic(t, func() { _ = slices.Concat(ss...) })
}
