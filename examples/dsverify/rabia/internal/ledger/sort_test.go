package ledger

// The VERIFICATION WORKAROUND G5 (sort.Sort over tallies instead of sort.Slice) gives the same order as the former
// sort.Slice call, on random tallies (distinct proposals, as PutRecvProposals keeps them).

import (
	"math/rand"
	"reflect"
	"sort"
	"testing"

	"rabia/internal/message"
)

func TestSortTalliesAsSortSlice(t *testing.T) {
	r := rand.New(rand.NewSource(1))
	for k := 0; k < 2000; k++ {
		n := r.Intn(12)
		seen := map[[2]uint32]bool{}
		var a []Tally
		for len(a) < n {
			id, seq := uint32(r.Intn(4)), uint32(r.Intn(6))
			if seen[[2]uint32{id, seq}] {
				continue
			}
			seen[[2]uint32{id, seq}] = true
			a = append(a, Tally{message.ConsensusObj{ProId: id, ProSeq: seq}, 1 + r.Intn(3)})
		}
		b := append([]Tally(nil), a...)
		sort.Slice(b, func(i, j int) bool {
			return b[i].Count > b[j].Count ||
				(b[i].Count == b[j].Count && message.ProxySeqIdLessThan(&b[i].Proposal, &b[j].Proposal))
		})
		s := &Slot{RecvProposals: a}
		s.SortRecvProposals()
		if !reflect.DeepEqual(s.RecvProposals, b) {
			t.Fatalf("%v != %v", s.RecvProposals, b)
		}
	}
}
