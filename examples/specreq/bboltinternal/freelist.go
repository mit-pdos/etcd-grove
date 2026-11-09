//go:build ignore

// Requirement snippets of bbolt's internal/freelist (batch 4d,
// Spec/go_etcd_io/bbolt/internal/freelist/): what bbolt (db.go, tx.go, node.go, bucket.go) relies
// on of the freelist, each reliance an explicit panic. The package is internal, so examples
// cannot import it: the snippets are written as if in it (package freelist), not built,
// gofmt-clean. Each takes a freelist made by NewArrayFreelist or NewHashMapFreelist: the specs
// are the interface's, the same for both.
//
// Common assumptions: the freelist's ids are below 2^36 (bbolt's high-water mark), so the
// counts are within flMaxIds; readers' txids are at least 1 (bbolt's metas start at txid 1).
package freelist

import (
	"unsafe"

	"go.etcd.io/bbolt/internal/common"
)

// pageAt is a page header over buf (DB.allocate's buffer, Tx.page's pages).
func pageAt(buf []byte, id common.Pgid, overflow uint32) *common.Page {
	p := (*common.Page)(unsafe.Pointer(&buf[0]))
	p.SetId(id)
	p.SetOverflow(overflow)
	return p
}

// REQ bboltinternal/alloc-free: an allocated run is no longer free; a page a later transaction
// frees is pending (Freed), not allocatable.
// Users: db.go:1238-1291 (DB.allocate: Allocate, 0 means grow), node.go:325 (spill), node.go:502
// (node.free), bucket.go:915 (Bucket.free), tx.go:217 (Commit: the old freelist page), tx.go:694
// (Tx.Page: Freed).
// Assumes: txid is not 0; buf is at least a page header.
// Specs: NewArrayFreelist, Interface.Init, Interface.Allocate, Interface.Freed, Interface.Free;
// common's Page.SetId/SetOverflow; laws: flOwn_wf.
func ReqAllocFree(txid common.Txid, buf []byte) {
	f := NewArrayFreelist()
	f.Init([]common.Pgid{3, 4, 5, 9})
	id := f.Allocate(txid, 2)
	if id == 0 {
		return // bbolt grows the file instead
	}
	if f.Freed(id) || f.Freed(id+1) {
		panic("alloc-free: allocated page still free")
	}
	f.Free(txid+1, pageAt(buf, id, 1))
	if !f.Freed(id) || !f.Freed(id+1) {
		panic("alloc-free: freed page not pending")
	}
	if r := f.Allocate(txid+1, 1); r == id || r == id+1 {
		panic("alloc-free: pending page allocated")
	}
}

// REQ bboltinternal/release-safe: a page freed while a reader that can see it is open is not
// released (so not reallocated); once the reader is gone, every pending page freed before all
// readers is released.
// Users: db.go:896 (beginTx: AddReadonlyTXID), db.go:957 (removeTx: RemoveReadonlyTXID),
// db.go:944 (beginRWTx: ReleasePendingPages, then the writer allocates).
// Assumes: f has no reader and no pending page; page id is at least 2 and in use (neither free
// nor pending), allocated by a transaction at or before 4 (or before the freelist was loaded);
// buf is at least a page header.
// Specs: Interface.AddReadonlyTXID, Interface.RemoveReadonlyTXID, Interface.Free,
// Interface.ReleasePendingPages, Interface.Allocate, Interface.PendingCount; laws: flOwn_wf,
// flReaders_perm.
func ReqReleaseSafe(f Interface, id common.Pgid, buf []byte) {
	f.AddReadonlyTXID(4) // a reader of the snapshot at txid 4: it sees page id
	f.Free(5, pageAt(buf, id, 0))
	f.ReleasePendingPages()
	for {
		r := f.Allocate(6, 1)
		if r == 0 {
			break
		}
		if r == id {
			panic("release-safe: page reused under a reader")
		}
	}
	f.RemoveReadonlyTXID(4)
	f.ReleasePendingPages()
	if f.PendingCount() != 0 {
		panic("release-safe: page freed before every reader still pending")
	}
}

// REQ bboltinternal/rollback: a rolled-back transaction's frees are undone (the pages are in use
// again, not pending) and the free pages are unchanged.
// Users: tx.go:318 (nonPhysicalRollback), tx.go:336-347 (rollback, then NoSyncReload or Reload).
// Assumes: page id is at least 2, in use (neither free nor pending) and not allocated by txid 7;
// txid 7 has freed nothing yet; buf is at least a page header.
// Specs: Interface.Free, Interface.Rollback, Interface.Freed, Interface.FreeCount.
func ReqRollback(f Interface, id common.Pgid, buf []byte) {
	n := f.FreeCount()
	f.Free(7, pageAt(buf, id, 0))
	f.Rollback(7)
	if f.Freed(id) {
		panic("rollback: page still pending")
	}
	if f.FreeCount() != n {
		panic("rollback: free pages changed")
	}
}

// REQ bboltinternal/reload-empty: a reload whose ids are all pending, or a re-Init with no ids,
// is allowed only when no page is free (the hash map's Init with no ids keeps its old cache):
// bbolt's reloads list every in-memory free page (the last commit's freelist page, or the pages no
// committed tree reaches), so their ids are empty only when nothing is free.
// Users: tx.go:336-347 (rollback), db.go:454-461 (loadFreelist).
// Assumes: f has no free page (every page it ever had free was allocated or is pending).
// Specs: Interface.Init, Interface.NoSyncReload, Interface.Freed.
func ReqReloadEmpty(f Interface) {
	f.NoSyncReload(nil)
	f.Init([]common.Pgid{})
	if f.FreeCount() != 0 {
		panic("reload-empty: free pages appeared")
	}
}

// REQ bboltinternal/write-reload: the freelist page Write leaves, in a buffer of
// EstimatedWritePageSize's pages, is a freelist page; a new freelist reading it has every free
// and pending page free; Reload on the writer's freelist gives back its free pages (the pending
// ones stay pending); NoSyncReload of the same ids does too.
// Users: tx.go:285-297 (commitFreelist: EstimatedWritePageSize, allocate, Write), db.go:454-461
// (loadFreelist: a new freelist, Read or Init), tx.go:336-347 (rollback: Reload, NoSyncReload).
// Assumes: pageSize is positive and at most 2^16 (bbolt's: 4096; a page size near 2^62 would
// overflow the buffer's size and make panic).
// Specs: Interface.EstimatedWritePageSize, Interface.Write, Interface.Count, Interface.FreeCount,
// NewHashMapFreelist, Interface.Read, Interface.Reload, Interface.Copyall,
// Interface.NoSyncReload; common's Page.IsFreelistPage; laws: freelistPage_read, flOwn_wf.
func ReqWriteReload(f Interface, pageSize int) {
	buf := make([]byte, (f.EstimatedWritePageSize()/pageSize+1)*pageSize)
	p := (*common.Page)(unsafe.Pointer(&buf[0]))
	f.Write(p)
	if !p.IsFreelistPage() {
		panic("write-reload: not a freelist page")
	}
	g := NewHashMapFreelist()
	g.Read(p)
	if g.FreeCount() != f.Count() {
		panic("write-reload: lost pages")
	}
	free := f.FreeCount()
	f.Reload(p)
	if f.FreeCount() != free {
		panic("write-reload: reload changed the free pages")
	}
	ids := make([]common.Pgid, f.Count())
	f.Copyall(ids)
	f.NoSyncReload(ids)
	if f.FreeCount() != free {
		panic("write-reload: no-sync reload changed the free pages")
	}
}
