package adt

import (
	"go.etcd.io/etcd/pkg/v3/adt"
)

// REQ adt/perm-cover: the auth store's permission cache: byte intervals and points inserted, then
// (read-only, shared by readers) whether a range request is covered by the union of the
// permissions, and whether a key is in one.
// Users: server/auth/range_perm_cache.go (getMergedPerms: Insert of NewBytesAffineInterval and
// NewBytesAffinePoint; checkKeyInterval: Contains; checkKeyPoint: Intersects).
// Assumes: none (the trees are this snippet's; afterwards read-only).
// Specs: NewIntervalTree.spec (at Cmp.bytes), NewBytesAffineInterval.spec,
// NewBytesAffinePoint.spec, intervalTree.Insert.spec, intervalTree.Contains.spec,
// intervalTree.Intersects.spec; laws: ivt_persist (the cache's trees read concurrently).
func ReqPermCover() {
	t := adt.NewIntervalTree()
	t.Insert(adt.NewBytesAffineInterval([]byte("a"), []byte("c")), struct{}{})
	t.Insert(adt.NewBytesAffineInterval([]byte("b"), []byte("e")), struct{}{})
	t.Insert(adt.NewBytesAffinePoint([]byte("x")), struct{}{})
	if !t.Contains(adt.NewBytesAffineInterval([]byte("a"), []byte("d"))) {
		panic("perm-cover: a range covered by two overlapping permissions refused")
	}
	if t.Contains(adt.NewBytesAffineInterval([]byte("a"), []byte("f"))) {
		panic("perm-cover: a range with an uncovered key granted")
	}
	if t.Contains(adt.NewBytesAffineInterval([]byte("a"), nil)) {
		panic("perm-cover: an open-ended range granted by bounded permissions")
	}
	if !t.Intersects(adt.NewBytesAffinePoint([]byte("x"))) || t.Intersects(adt.NewBytesAffinePoint([]byte("y"))) {
		panic("perm-cover: a point permission misread")
	}
}
