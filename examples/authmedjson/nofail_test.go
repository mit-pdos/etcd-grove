package authmedjson

import (
	"encoding/json"
	"math"
	"strings"
	"sync"
	"testing"
	"unsafe"

	"go.etcd.io/etcd/client/pkg/v3/types"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
)

func mustOK(t *testing.T, v any) []byte {
	b, err := json.Marshal(v)
	if err != nil {
		panic("claim: no error: " + err.Error())
	}
	return b
}

func members() []membership.Member {
	bad := []string{"\xff", "\xc3", "a\x00b", string([]byte{0xed, 0xa0, 0x80}), "<>&  ", "\"\\", strings.Repeat("\xfe", 1000)}
	var ms []membership.Member
	for _, id := range []types.ID{0, 1, math.MaxUint64, 1 << 63} {
		for _, l := range []bool{false, true} {
			ms = append(ms,
				membership.Member{ID: id},
				membership.Member{ID: id, RaftAttributes: membership.RaftAttributes{PeerURLs: []string{}, IsLearner: l}, Attributes: membership.Attributes{ClientURLs: []string{}}},
				membership.Member{ID: id, RaftAttributes: membership.RaftAttributes{PeerURLs: bad, IsLearner: l}, Attributes: membership.Attributes{Name: strings.Join(bad, ""), ClientURLs: bad}},
				membership.Member{ID: id, RaftAttributes: membership.RaftAttributes{PeerURLs: []string{"", ""}}, Attributes: membership.Attributes{Name: "\xff"}},
			)
		}
	}
	return ms
}

// (2) never erroring, over invalid UTF-8, control bytes, surrogates, max IDs, nil/empty.
func TestNoError(t *testing.T) {
	for _, m := range members() {
		mustOK(t, m)
		for _, p := range []bool{false, true} {
			mustOK(t, membership.ConfigChangeContext{Member: m, IsPromote: p})
		}
	}
	b := mustOK(t, members()[2])
	t.Logf("%q", b[:120])
}

// (2) large inputs: many elements and a long string.
func TestNoErrorLarge(t *testing.T) {
	big := make([]string, 1<<20)
	for i := range big {
		big[i] = "\xff\x01<"
	}
	long := strings.Repeat("\x01\xff", 1<<24)
	m := membership.Member{ID: math.MaxUint64, RaftAttributes: membership.RaftAttributes{PeerURLs: big}, Attributes: membership.Attributes{Name: long, ClientURLs: []string{long}}}
	b := mustOK(t, m)
	mustOK(t, membership.ConfigChangeContext{Member: m})
	t.Logf("len %d", len(b))
}

func overlaps(a, b []byte) bool {
	if cap(a) == 0 || cap(b) == 0 {
		return false
	}
	pa, pb := uintptr(unsafe.Pointer(unsafe.SliceData(a))), uintptr(unsafe.Pointer(unsafe.SliceData(b)))
	return pa < pb+uintptr(cap(b)) && pb < pa+uintptr(cap(a))
}

func overlapsStr(a []byte, s string) bool {
	if cap(a) == 0 || len(s) == 0 {
		return false
	}
	pa, ps := uintptr(unsafe.Pointer(unsafe.SliceData(a))), uintptr(unsafe.Pointer(unsafe.StringData(s)))
	return pa < ps+uintptr(len(s)) && ps < pa+uintptr(cap(a))
}

// (1) freshness: the result (incl. spare capacity) aliases no other result and no input string;
// writing into it and appending into its capacity does not change a later call's result nor the input.
func TestFresh(t *testing.T) {
	m := membership.Member{ID: 5, RaftAttributes: membership.RaftAttributes{PeerURLs: []string{"http://a:1"}}, Attributes: membership.Attributes{Name: "n", ClientURLs: []string{"http://c:2"}}}
	var outs [][]byte
	for i := 0; i < 1000; i++ {
		outs = append(outs, mustOK(t, m), mustOK(t, membership.ConfigChangeContext{Member: m}))
	}
	for i := range outs {
		for j := i + 1; j < len(outs); j++ {
			if overlaps(outs[i], outs[j]) {
				panic("claim: fresh (two results alias)")
			}
		}
		for _, s := range []string{m.PeerURLs[0], m.ClientURLs[0], m.Name} {
			if overlapsStr(outs[i], s) {
				panic("claim: fresh (result aliases an input string)")
			}
		}
	}
	ref := string(mustOK(t, m))
	a := mustOK(t, m)
	for i := range a {
		a[i] = 'X'
	}
	a = append(a[:cap(a)], make([]byte, 64)...)
	_ = a
	b := mustOK(t, m)
	b = append(b, strings.Repeat("Y", cap(b)-len(b))...)
	if string(mustOK(t, m)) != ref || m.PeerURLs[0] != "http://a:1" || m.ClientURLs[0] != "http://c:2" {
		panic("claim: writes to a result are invisible elsewhere")
	}
	t.Logf("len %d cap %d", len(b), cap(b))
}

// (1) Marshal does not retain or write to the borrowed slices: after it returns, the
// caller writes them; a later result reflects the new contents, earlier result unchanged.
func TestNoRetain(t *testing.T) {
	ps := []string{"p"}
	cs := []string{"c"}
	m := membership.Member{RaftAttributes: membership.RaftAttributes{PeerURLs: ps}, Attributes: membership.Attributes{ClientURLs: cs}}
	r1 := string(mustOK(t, m))
	ps[0], cs[0] = "P2", "C2"
	r2 := string(mustOK(t, m))
	if r1 == r2 || ps[0] != "P2" || cs[0] != "C2" {
		panic("claim: no retention")
	}
}

// (1) concurrent calls on the same member, sharing the slices read-only (fractional borrow);
// run with -race.
func TestConcurrentReaders(t *testing.T) {
	m := membership.Member{ID: 9, RaftAttributes: membership.RaftAttributes{PeerURLs: []string{"a", "b"}}, Attributes: membership.Attributes{ClientURLs: []string{"c"}}}
	var wg sync.WaitGroup
	for i := 0; i < 16; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for j := 0; j < 1000; j++ {
				mustOK(t, m)
				mustOK(t, membership.ConfigChangeContext{Member: m})
			}
		}()
	}
	wg.Wait()
}
