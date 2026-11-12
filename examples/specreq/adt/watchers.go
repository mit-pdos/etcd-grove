// Package adt holds the requirement snippets of etcd's interval tree (pkg/v3/adt, batch 3f):
// what its users (mvcc's watcher groups, the auth store's permission cache, the gRPC layer's
// duplicate-key check) rely on.
package adt

import (
	"go.etcd.io/etcd/pkg/v3/adt"
)

type set map[int]struct{}

// REQ adt/range-watchers: the watcher groups' use: a range's value found by its exact interval and
// updated in place (a map), a new range inserted, the ranges a key's point stabs, whether a key
// is in some range, a range deleted (true when present).
// Users: server/storage/mvcc/watcher_group.go (add: Find then add to the set, else Insert;
// contains: Intersects of a point; watcherSetByKey: Stab of a point; delete: Find, Delete).
// Assumes: none (the tree is this snippet's).
// Specs: NewIntervalTree.spec, NewStringAffineInterval.spec, NewStringAffinePoint.spec,
// intervalTree.Insert.spec, intervalTree.Find.spec, intervalTree.Stab.spec,
// intervalTree.Intersects.spec, intervalTree.Delete.spec; laws: ivt_sorted.
func ReqRangeWatchers() {
	t := adt.NewIntervalTree()
	ab := adt.NewStringAffineInterval("a", "b")
	if t.Find(ab) != nil {
		panic("range-watchers: found in an empty tree")
	}
	t.Insert(ab, set{1: {}})
	t.Insert(adt.NewStringAffineInterval("a", ""), set{2: {}}) // from "a" on
	iv := t.Find(ab)
	if iv == nil {
		panic("range-watchers: an inserted range not found")
	}
	iv.Val.(set)[3] = struct{}{}
	ivs := t.Stab(adt.NewStringAffinePoint("a1"))
	if len(ivs) != 2 {
		panic("range-watchers: a range containing the key missed")
	}
	n := 0
	for _, v := range ivs {
		n += len(v.Val.(set))
	}
	if n != 3 {
		panic("range-watchers: an update of a found value lost")
	}
	if len(t.Stab(adt.NewStringAffinePoint("b"))) != 1 {
		panic("range-watchers: an end is excluded, an empty end unbounded")
	}
	if t.Intersects(adt.NewStringAffinePoint("0")) {
		panic("range-watchers: a key below every range")
	}
	if !t.Delete(ab) || t.Delete(ab) {
		panic("range-watchers: a delete of a present range failed, or of an absent one succeeded")
	}
	if len(t.Stab(adt.NewStringAffinePoint("a1"))) != 1 {
		panic("range-watchers: a deleted range still stabbed")
	}
}
