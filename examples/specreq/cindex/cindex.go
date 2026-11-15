// Requirement snippets for etcdserver/cindex, the consistent index (batch 2d).
package cindex

import (
	"go.etcd.io/etcd/server/v3/etcdserver/cindex"
	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// REQ cindex/apply-moves-index: the apply thread marks the entry it applies (the applying index),
// and once the entry is applied the consistent index is that entry's.
// Users: server/etcdserver/server.go:1925-1938 (apply), 1970-1980 (applyEntryNormal's defer),
// 2042-2043 (applyConfChange), 2478-2484 (the post-lock hook).
// Assumes: the caller is the indexer's only writer (ciWriter).
// Specs: consistentIndex.{SetConsistentApplyingIndex,ConsistentApplyingIndex,SetConsistentIndex,
// ConsistentIndex}.spec.
func ReqApplyMovesIndex(ci cindex.ConsistentIndexer, k, t uint64) {
	ci.SetConsistentApplyingIndex(k, t)
	if a, _ := ci.ConsistentApplyingIndex(); a != k {
		panic("apply-moves-index: applying index lost")
	}
	ci.SetConsistentIndex(k, t)
	if k != 0 && ci.ConsistentIndex() != k {
		panic("apply-moves-index: consistent index lost")
	}
}

// REQ cindex/reload-after-setbackend: pointed at a new backend, the indexer reports that backend's
// stored index (the snapshot install, bootstrap).
// Users: server/etcdserver/server.go:1080, 1100 (applySnapshot), bootstrap.go:257-273.
// Assumes: be's stored consistent index is v and nothing commits to be meanwhile; the caller is the
// only writer.
// Specs: consistentIndex.SetBackend.spec, consistentIndex.ConsistentIndex.spec; 4b's
// ReadConsistentIndex (beStoredCI).
func ReqReloadAfterSetBackend(ci cindex.ConsistentIndexer, be cindex.Backend, v uint64) {
	ci.SetBackend(be)
	if ci.ConsistentIndex() != v {
		panic("reload-after-setbackend: not the backend's index")
	}
}

// REQ cindex/save-in-commit: the backend's pre-commit hook writes the in-memory index into the
// commit (unless it is 0), never a lower one than the transaction holds.
// Users: server/storage/hooks.go:46 (OnPreCommitUnsafe).
// Assumes: tx is the batch transaction, locked; k is at least the index tx holds; the caller is
// the indexer's only writer (here; in etcd, the apply thread writes concurrently).
// Specs: consistentIndex.UnsafeSave.spec (txStoredCI), 4b's UnsafeReadConsistentIndex.
func ReqSaveInCommit(ci cindex.ConsistentIndexer, tx backend.UnsafeReadWriter, k, t uint64) {
	ci.SetConsistentIndex(k, t)
	ci.UnsafeSave(tx)
	if v, _ := schema.UnsafeReadConsistentIndex(tx); k != 0 && v != k {
		panic("save-in-commit: index not saved")
	}
}
