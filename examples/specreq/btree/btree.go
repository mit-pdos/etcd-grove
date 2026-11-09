// Package btree holds the requirement snippets of the k8s fork of google/btree
// (k8s.io/utils/third_party/forked/golang/btree; batch 1g, Spec/k8s_io/utils/third_party/forked/golang/btree/):
// what etcd's cache (cache/store.go, cache/snapshot.go) relies on, each reliance an explicit panic.
//
// Common assumptions: none beyond the specs' preconditions (a degree in [2, 2^62]).
package btree

import (
	"k8s.io/utils/third_party/forked/golang/btree"
)

// item is the cache's kvItem: a key and a payload, ordered by key.
type item struct {
	key string
	val int
}

func itemLess(a, b *item) bool { return a.key < b.key }

// REQ btree/sorted-map: the tree is a map from keys to the last item put; a delete removes the
// key (and reports whether it was there); point reads and range reads see exactly the map, in key
// order.
// Users: cache/store.go:109-111 (Restore), :154-162 (applyEventsLocked), cache/snapshot.go:33-55
// (Range: Get, AscendGreaterOrEqual, AscendRange).
// Assumes: nothing.
// Specs: New.spec, BTree.ReplaceOrInsert.spec, BTree.Delete.spec, BTree.Get.spec,
// BTree.AscendGreaterOrEqual.spec, BTree.AscendRange.spec; laws: ownBTree_sorted, ownBTree_items.
func ReqSortedMap() {
	t := btree.New[*item](32, itemLess)
	t.ReplaceOrInsert(&item{key: "b", val: 1})
	t.ReplaceOrInsert(&item{key: "a", val: 2})
	t.ReplaceOrInsert(&item{key: "c", val: 3})
	if old, ok := t.ReplaceOrInsert(&item{key: "b", val: 4}); !ok || old.val != 1 {
		panic("sorted-map: replace lost the old item")
	}
	if _, ok := t.Delete(&item{key: "c"}); !ok {
		panic("sorted-map: delete of a present key reported absent")
	}
	if _, ok := t.Delete(&item{key: "c"}); ok {
		panic("sorted-map: delete of an absent key reported present")
	}
	if it, ok := t.Get(&item{key: "b"}); !ok || it.val != 4 {
		panic("sorted-map: point read")
	}
	var keys []string
	t.AscendGreaterOrEqual(&item{key: "a"}, func(it *item) bool {
		keys = append(keys, it.key)
		return true
	})
	if len(keys) != 2 || keys[0] != "a" || keys[1] != "b" {
		panic("sorted-map: from-key read")
	}
	var inRange []string
	t.AscendRange(&item{key: "a"}, &item{key: "b"}, func(it *item) bool {
		inRange = append(inRange, it.key)
		return true
	})
	if len(inRange) != 1 || inRange[0] != "a" {
		panic("sorted-map: range read")
	}
}

// REQ btree/frozen-clone: a clone keeps the entries the original had when it was cloned, whatever
// is written to the original after; the clone may be read from another goroutine while the
// original is written (the cache's snapshots, read by Gets outside the store's lock).
// Users: cache/snapshot.go:29-31 (newClonedSnapshot), cache/store.go:89-96 (getSnapshot hands a
// snapshot out; Get reads it after the read lock is released).
// Assumes: nothing.
// Specs: BTree.Clone.spec, BTree.Get.spec, BTree.ReplaceOrInsert.spec, BTree.Delete.spec; laws:
// ownBTree_persist, ownBTree_discard_persistent.
func ReqFrozenClone() {
	t := btree.New[*item](2, itemLess)
	for i, k := range []string{"a", "b", "c", "d", "e"} {
		t.ReplaceOrInsert(&item{key: k, val: i})
	}
	snap := t.Clone()
	done := make(chan struct{})
	go func() {
		if it, ok := snap.Get(&item{key: "c"}); !ok || it.val != 2 {
			panic("frozen-clone: the clone changed")
		}
		close(done)
	}()
	t.ReplaceOrInsert(&item{key: "c", val: 9})
	t.Delete(&item{key: "a"})
	<-done
	if it, ok := snap.Get(&item{key: "a"}); !ok || it.val != 0 {
		panic("frozen-clone: a write to the original reached the clone")
	}
}

// REQ btree/ordered: a tree of an ordered type by its `<` (NewOrdered, Less).
// Users: none in etcd (kept: the methods were verified).
// Assumes: nothing.
// Specs: NewOrdered.spec, BTree.ReplaceOrInsert.spec, BTree.Min.spec, BTree.Max.spec,
// BTree.Len.spec.
func ReqOrdered() {
	t := btree.NewOrdered[int](4)
	for _, x := range []int{5, 1, 3} {
		t.ReplaceOrInsert(x)
	}
	if m, ok := t.Min(); !ok || m != 1 {
		panic("ordered: min")
	}
	if m, ok := t.Max(); !ok || m != 5 {
		panic("ordered: max")
	}
	if t.Len() != 3 {
		panic("ordered: len")
	}
}

// snap is Kubernetes' btreeStore as its snapshotter keeps it: a frozen clone of the store's tree,
// ordered by its resource version.
type snap struct {
	rv   uint64
	tree *btree.BTree[*item]
}

func snapLess(a, b *snap) bool { return a.rv < b.rv }

// REQ btree/tree-of-snapshots: a tree whose items are frozen clones, keyed by an immutable
// resource version: DescendLessOrEqual stopping at the first item finds the newest snapshot at or
// below a version, and that snapshot's tree still reads as it was when cloned; Min and DeleteMin
// drop the oldest; Clear empties the tree.
// Users: k8s.io/apiserver/pkg/storage/cacher/store/snapshotter.go:65-170 (newSnapshotter,
// GetSnapshot's DescendLessOrEqual, HasSnapshot's Min, RemoveLess's Min/DeleteMin, reset's
// Clear(false), Add's ReplaceOrInsert), store/btree.go:41-121 (Clone, Delete, ReplaceOrInsert,
// AscendGreaterOrEqual on the store's tree). Translated with bodies in
// Code/k8s_io/apiserver/pkg/storage/cacher/store.lean; its specs are not on this branch.
// Assumes: nothing.
// Specs: New.spec, BTree.Clone.spec, BTree.ReplaceOrInsert.spec, BTree.Delete.spec,
// BTree.DescendLessOrEqual.spec, BTree.Get.spec, BTree.Min.spec, BTree.DeleteMin.spec,
// BTree.Clear.spec, BTree.Len.spec; laws: ownBTree_persist (an item's predicate holds the frozen
// inner tree at DFrac.discard, persistent).
func ReqTreeOfSnapshots() {
	store := btree.New[*item](4, itemLess)
	snaps := btree.New[*snap](4, snapLess)
	for i, k := range []string{"a", "b", "c"} {
		store.ReplaceOrInsert(&item{key: k, val: i + 1})
		snaps.ReplaceOrInsert(&snap{rv: uint64(i + 1), tree: store.Clone()})
	}
	store.Delete(&item{key: "a"})
	var found *snap
	snaps.DescendLessOrEqual(&snap{rv: 2}, func(s *snap) bool {
		found = s
		return false
	})
	if found == nil || found.rv != 2 {
		panic("tree-of-snapshots: not the newest snapshot at or below the version")
	}
	if it, ok := found.tree.Get(&item{key: "a"}); !ok || it.val != 1 {
		panic("tree-of-snapshots: a snapshot changed after a write to the store")
	}
	if _, ok := found.tree.Get(&item{key: "c"}); ok {
		panic("tree-of-snapshots: a snapshot sees a later write")
	}
	if oldest, ok := snaps.Min(); !ok || oldest.rv != 1 {
		panic("tree-of-snapshots: Min is not the oldest")
	}
	if oldest, ok := snaps.DeleteMin(); !ok || oldest.rv != 1 || snaps.Len() != 2 {
		panic("tree-of-snapshots: DeleteMin did not drop the oldest")
	}
	snaps.Clear(false)
	if snaps.Len() != 0 {
		panic("tree-of-snapshots: Clear left items")
	}
}
