package reflect

// sort.Slice and sort.SliceIsSorted: a slice of any type sorted through
// reflectlite.Swapper.
//
// Mirrors:
//   - etcd server/v3 storage/mvcc/hash.go:165 (`sort.Slice(s.hashes, func(i, j int) bool
//     { return s.hashes[i].Revision < s.hashes[j].Revision })`, a []KeyValueHash);
//   - etcd server/v3 etcdserver/corrupt.go:423 (hashes sorted descending);
//   - bbolt internal/freelist/hashmap.go:34 (`sort.SliceIsSorted(pgids, ...)`, a []Pgid);
//   - Go 1.27.3 sort/slice.go:25-27,42-44,53-54 (`rv := reflectlite.ValueOf(x); swap :=
//     reflectlite.Swapper(x); length := rv.Len()`) and internal/reflectlite/
//     swapper.go (Swapper: panics on a non-slice; for length 0 a swap panics
//     "reflect: slice index out of range", for length 1 unless i == j == 0;
//     otherwise per element size, through unsafe: pointer words, strings,
//     8/4/2/1-byte words, typedmemmove).
//
// To prove: sort.Slice permutes the slice in place (the caller's backing
// array) into an order where less is false of every adjacent pair, for a
// strict weak order; SliceIsSorted is that test; neither panics on a slice.
// Swapper's own unsafe is internal: a semantics may take Swapper (swap two
// elements of a slice of any element type) as a primitive.
//
// Needs R2 on reflectlite (ValueOf, Len, Swapper on any slice type).

import "sort"

type KeyValueHash struct {
	Hash     uint32
	Revision int64
}

// REQ reflect/sort-slice: sort.Slice sorts a []KeyValueHash in place by revision (ascending, and
// descending as corrupt.go does), a slice of zero or one element is left alone, and
// SliceIsSorted agrees.
// Users: etcd storage/mvcc/hash.go:165, etcdserver/corrupt.go:423; bbolt
// internal/freelist/hashmap.go:34.
// Assumes: nothing.
// Specs: none yet; needs reflectlite's Swapper and Len (doc.go).
func ReqSortSlice() {
	hashes := []KeyValueHash{{1, 30}, {2, 10}, {3, 20}}
	alias := hashes
	sort.Slice(hashes, func(i, j int) bool { return hashes[i].Revision < hashes[j].Revision })
	if alias[0].Revision != 10 || alias[1].Revision != 20 || alias[2].Hash != 1 {
		panic("sort-slice: ascending, in place")
	}
	sort.Slice(hashes, func(i, j int) bool { return hashes[i].Revision > hashes[j].Revision })
	if hashes[0].Revision != 30 || hashes[2].Revision != 10 {
		panic("sort-slice: descending")
	}
	var none []KeyValueHash
	sort.Slice(none, func(i, j int) bool { return false })
	one := []Pgid{7}
	sort.Slice(one, func(i, j int) bool { return one[i] < one[j] })
	pgids := []Pgid{3, 5, 9}
	if !sort.SliceIsSorted(pgids, func(i, j int) bool { return pgids[i] < pgids[j] }) {
		panic("sort-slice: SliceIsSorted")
	}
	pgids[0] = 10
	if sort.SliceIsSorted(pgids, func(i, j int) bool { return pgids[i] < pgids[j] }) {
		panic("sort-slice: not sorted")
	}
}

// REQ reflect/sort-slice (panics): sort.Slice of a non-slice panics (reflectlite's ValueError
// "reflect: call of Swapper on int Value").
// Specs: none yet.
func MustPanicSortNotSlice() {
	sort.Slice(3, func(i, j int) bool { return false })
}
