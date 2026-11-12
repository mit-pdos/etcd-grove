package adt

import (
	"go.etcd.io/etcd/pkg/v3/adt"
)

// REQ adt/nested-deletes: the duplicate-key check: a level's deletes (ranges and points) with a
// nested transaction's merged in over the whole key space (Union), then whether a put's key is
// under some delete.
// Users: server/etcdserver/api/v3rpc/key.go (checkIntervals: Insert of the level's deletes,
// Union of each branch's, Intersects of each put's point).
// Assumes: none (the trees are this snippet's).
// Specs: NewIntervalTree.spec, NewStringAffineInterval.spec, NewStringAffinePoint.spec,
// intervalTree.Insert.spec, intervalTree.Union.spec, intervalTree.Intersects.spec.
func ReqNestedDeletes() {
	dels := adt.NewIntervalTree()
	dels.Insert(adt.NewStringAffinePoint("k"), struct{}{})
	inner := adt.NewIntervalTree()
	inner.Insert(adt.NewStringAffineInterval("m", "p"), struct{}{})
	inner.Insert(adt.NewStringAffineInterval("z", ""), struct{}{})
	dels.Union(inner, adt.NewStringAffineInterval("\x00", ""))
	if dels.Len() != 3 {
		panic("nested-deletes: a nested delete lost in the union")
	}
	for _, k := range []string{"k", "n", "zz"} {
		if !dels.Intersects(adt.NewStringAffinePoint(k)) {
			panic("nested-deletes: a put under a delete accepted")
		}
	}
	for _, k := range []string{"j", "p", "y"} {
		if dels.Intersects(adt.NewStringAffinePoint(k)) {
			panic("nested-deletes: a put under no delete refused")
		}
	}
	if !inner.Intersects(adt.NewStringAffinePoint("n")) {
		panic("nested-deletes: the union changed its argument")
	}
}
