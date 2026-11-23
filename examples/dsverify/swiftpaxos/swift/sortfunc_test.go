package swift

import (
	"math/rand"
	"slices"
	"sort"
	"testing"
)

// The sorts moved from sort.Slice to slices.SortFunc (verification workaround) sort by strict
// total orders on distinct elements, so the result is the same: checked on random inputs.
func TestSortFuncSameAsSortSlice(t *testing.T) {
	rng := rand.New(rand.NewSource(1))
	for n := 0; n < 200; n++ {
		seen := map[CommandId]bool{}
		var ids []CommandId
		for len(ids) < rng.Intn(20) {
			id := CommandId{ClientId: int32(rng.Intn(5)), SeqNum: int32(rng.Intn(5))}
			if !seen[id] {
				seen[id] = true
				ids = append(ids, id)
			}
		}
		a := slices.Clone(ids)
		b := slices.Clone(ids)
		sort.Slice(a, func(i, j int) bool { return cmdIdLess(a[i], a[j]) })
		slices.SortFunc(b, cmdIdCmp)
		if !slices.Equal(a, b) {
			t.Fatalf("%v: sort.Slice %v, SortFunc %v", ids, a, b)
		}
	}
}
