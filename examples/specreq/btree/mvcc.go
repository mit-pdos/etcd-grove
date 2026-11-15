package btree

import (
	"sync"

	"k8s.io/utils/third_party/forked/golang/btree"
)

// keyIdx is mvcc's keyIndex: an immutable key and fields the index mutates in place.
type keyIdx struct {
	key  string
	revs int
}

func keyIdxLess(a, b *keyIdx) bool { return a.key < b.key }

// REQ btree/mutate-in-place: Get returns the stored pointer itself; the caller mutates its fields
// other than the key and the change is what a later Get sees (the order is on the key only).
// Users: server/v3/storage/mvcc/index.go:54-64 (Put: okeyi.put), :192-203 (Tombstone).
// Assumes: nothing.
// Specs: New.spec, BTree.ReplaceOrInsert.spec, BTree.Get.spec (mLookup returns the stored item;
// ItemOrder.item persistent on the key only).
func ReqMutateInPlace() {
	t := btree.New[*keyIdx](32, keyIdxLess)
	t.ReplaceOrInsert(&keyIdx{key: "a", revs: 1})
	it, ok := t.Get(&keyIdx{key: "a"})
	if !ok {
		panic("mutate-in-place: lost item")
	}
	it.revs++
	it2, ok := t.Get(&keyIdx{key: "a"})
	if !ok || it2 != it || it2.revs != 2 {
		panic("mutate-in-place: Get did not return the stored item")
	}
}

// REQ btree/fractional-readers: readers holding a read lock read the live tree at once (Get,
// AscendGreaterOrEqual); a writer under the write lock then changes it.
// Users: server/v3/storage/mvcc/index.go:66-70 (Get), :112-187 (Revisions, CountRevisions, Range),
// :54-64 (Put).
// Assumes: nothing (the lock's invariant holds the tree's whole share; each reader takes a fraction).
// Specs: BTree.Get.spec, BTree.AscendGreaterOrEqual.spec at a fraction; laws: ownBTree_fractional,
// ownBTree_agree.
func ReqFractionalReaders() {
	var mu sync.RWMutex
	t := btree.New[*keyIdx](32, keyIdxLess)
	t.ReplaceOrInsert(&keyIdx{key: "a"})
	t.ReplaceOrInsert(&keyIdx{key: "b"})
	var wg sync.WaitGroup
	for i := 0; i < 2; i++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			mu.RLock()
			defer mu.RUnlock()
			if _, ok := t.Get(&keyIdx{key: "a"}); !ok {
				panic("fractional-readers: point read")
			}
			n := 0
			t.AscendGreaterOrEqual(&keyIdx{key: "a"}, func(*keyIdx) bool { n++; return true })
			if n < 2 {
				panic("fractional-readers: range read")
			}
		}()
	}
	wg.Wait()
	mu.Lock()
	t.ReplaceOrInsert(&keyIdx{key: "c"})
	mu.Unlock()
}

// REQ btree/stop-early: an iteration whose callback returns false at the end key visits exactly the
// keys in [start, end), in order.
// Users: server/v3/storage/mvcc/index.go:95-108 (unsafeVisit), :112-134 (Revisions' limit),
// :241-258 (Equal).
// Assumes: nothing.
// Specs: BTree.AscendGreaterOrEqual.spec (iterProtocol, iterDone with stopped).
func ReqStopEarly() {
	t := btree.New[*keyIdx](2, keyIdxLess)
	for _, k := range []string{"a", "b", "c", "d"} {
		t.ReplaceOrInsert(&keyIdx{key: k})
	}
	var got []string
	t.AscendGreaterOrEqual(&keyIdx{key: "b"}, func(it *keyIdx) bool {
		if it.key >= "d" {
			return false
		}
		got = append(got, it.key)
		return true
	})
	if len(got) != 2 || got[0] != "b" || got[1] != "c" {
		panic("stop-early: wrong keys visited")
	}
}

// REQ btree/compact-clone: a clone taken under the lock is iterated without it while the callback
// re-takes the lock and deletes each visited item from the original (which must still hold it),
// and another goroutine inserts new keys into the original under the lock.
// Users: server/v3/storage/mvcc/index.go:205-229 (Compact: lg.Panic unless the delete found it).
// Assumes: only this function deletes from the original (mvcc's: Compact is the only deleter).
// Specs: BTree.Clone.spec, BTree.Ascend.spec, BTree.Delete.spec (ok = the key present),
// BTree.ReplaceOrInsert.spec; laws: ownBTree_persist (the clone, read-only), ownBTree_items.
func ReqCompactClone() {
	var mu sync.Mutex
	t := btree.New[*keyIdx](2, keyIdxLess)
	for _, k := range []string{"a", "b", "c"} {
		t.ReplaceOrInsert(&keyIdx{key: k})
	}
	mu.Lock()
	clone := t.Clone()
	mu.Unlock()
	done := make(chan struct{})
	go func() {
		mu.Lock()
		t.ReplaceOrInsert(&keyIdx{key: "z"})
		mu.Unlock()
		close(done)
	}()
	clone.Ascend(func(it *keyIdx) bool {
		mu.Lock()
		if _, ok := t.Delete(it); !ok {
			panic("compact-clone: a cloned key missing from the original")
		}
		mu.Unlock()
		return true
	})
	<-done
	mu.Lock()
	if t.Len() != 1 {
		panic("compact-clone: the original lost or kept the wrong keys")
	}
	mu.Unlock()
}
