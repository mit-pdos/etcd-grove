// An assignment between partially overlapping slice-to-array-pointer views,
// one side of a named array type: gc before the fix of golang/go#78371 copies
// forward in place instead of loading the right side first. Run in any module:
// go test -run TestOverlappingNamedArrayCopy -v
package overlap

import (
	"slices"
	"testing"
)

type A [4]int

func TestOverlappingNamedArrayCopy(t *testing.T) {
	s := []int{0, 1, 2, 3, 4}
	*(*A)(s[1:5]) = *(*[4]int)(s[0:4])
	if want := []int{0, 0, 1, 2, 3}; !slices.Equal(s, want) {
		t.Errorf("s = %v, want %v", s, want)
	}
}

// The same copy between identical array types (fixed by golang/go#54467): passes.
func TestOverlappingUnnamedArrayCopy(t *testing.T) {
	s := []int{0, 1, 2, 3, 4}
	*(*[4]int)(s[1:5]) = *(*[4]int)(s[0:4])
	if want := []int{0, 0, 1, 2, 3}; !slices.Equal(s, want) {
		t.Errorf("s = %v, want %v", s, want)
	}
}
