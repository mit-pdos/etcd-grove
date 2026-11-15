package mvcc

import (
	smvcc "go.etcd.io/etcd/server/v3/storage/mvcc"
)

// REQ mvcc/hash: the store's hash storage answers the corruption checker and the maintenance
// server without panicking, concurrently with writes and compactions (not with a restore) (its answers are
// compared across members, never trusted by a safety argument).
// Users: server/etcdserver/corrupt.go:97, 180, 193, 421, 550 (HashByRev, Hashes),
// api/v3rpc/maintenance.go:233, 243 (Hash, HashByRev), server.go:367 (HashStorage), the store's
// compaction job (Store).
// Assumes: a reader token for each HashByRev and Hash, and no Restore concurrently (a share of
// mvccRestoreGate: the server's snapshot install excludes hashing).
// Specs: store.HashStorage.spec, hashStorage.{HashByRev,Hash,Hashes,Store}.spec (trusted: the hashing
// is translated names-only).
func ReqHash(kv smvcc.KV, rev int64) {
	hs := kv.HashStorage()
	h, _, err := hs.HashByRev(rev)
	if err == nil {
		hs.Store(h)
	}
	_, _, _ = hs.Hash()
	for _, x := range hs.Hashes() {
		_ = x.Revision
	}
}
