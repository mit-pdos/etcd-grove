package mvcc

import (
	"go.uber.org/zap"

	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage/backend"
	smvcc "go.etcd.io/etcd/server/v3/storage/mvcc"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// REQ mvcc/boot-fresh: a fresh member's store over a backend whose Meta bucket the server created
// first starts empty at revision 1, never compacted.
// Users: server/etcdserver/bootstrap.go:266 (schema.CreateMetaBucket before mvcc.New),
// server.go:366.
// Assumes: be is a fresh backend (no Key bucket, nothing in Meta's compaction keys); le a lessor over
// it; a reader token for each Rev/FirstRev.
// Specs: NewStore.spec (mvccStorageFor of an empty image whichever buckets exist: mvccImage_empty),
// store.Rev.spec, store.FirstRev.spec.
func ReqBootFresh(lg *zap.Logger, be backend.Backend, le lease.Lessor) smvcc.KV {
	schema.CreateMetaBucket(be.BatchTx())
	kv := smvcc.NewStore(lg, be, le, smvcc.StoreConfig{})
	if kv.Rev() != 1 || kv.FirstRev() != -1 {
		panic("boot-fresh: a fresh store is not at revision 1, uncompacted")
	}
	return kv
}

// REQ mvcc/boot-no-meta: a store over a fresh backend whose Meta bucket nobody created (NewStore
// creates it itself, under its batch lock, kvstore.go:121-123) starts empty at revision 1, never
// compacted.
// Users: examples/mvccrand/mvccrand.go:809-811 (backend.New, lease.NewLessor, mvcc.New; no
// schema.CreateMetaBucket).
// Assumes: be is a fresh backend (no Key or Meta bucket); le a lessor over it; a reader token for
// each Rev/FirstRev.
// Specs: New.spec (mvccStorageFor of an empty image, Meta's existence conditional: mvccImage_empty),
// keyBackend_intro (4a: its case with Meta not yet made, requested of backend-schema, A10 F2),
// watchableStore.Rev.spec, watchableStore.FirstRev.spec.
func ReqBootNoMeta(lg *zap.Logger, be backend.Backend, le lease.Lessor) smvcc.WatchableKV {
	kv := smvcc.New(lg, be, le, smvcc.StoreConfig{})
	if kv.Rev() != 1 || kv.FirstRev() != -1 {
		panic("boot-no-meta: a fresh store is not at revision 1, uncompacted")
	}
	return kv
}

// REQ mvcc/compactor-rev: a goroutine that outlives the store (the server's compactor) calls Rev()
// at any time, also after Close and after the backend's close, with a reader token turned for good
// into a Rev token; the shutdown takes every other token.
// Users: server/etcdserver/api/v3compactor/revision.go:81, periodic.go:110 (rg.Rev()), server.go:950-961
// (Cleanup: kv.Close, the backend's close, then the compactor's Stop).
// Assumes: the caller turned one reader token into a Rev token (mvccRevTok_of) for this goroutine;
// the rest of the shutdown (mvccClosed_rest with the others) is the server's.
// Specs: store.Rev.spec (revRd γ true), mvccRevTok_of, mvccClosed_rest.
func ReqCompactorRev(kv smvcc.KV, be backend.Backend, last int64) {
	if kv.Rev() < last {
		panic("compactor-rev: the revision went down")
	}
	if err := kv.Close(); err != nil {
		panic("compactor-rev: Close failed")
	}
	be.Close()
	_ = kv.Rev() // after both closes: no panic
}
