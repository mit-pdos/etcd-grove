package mvcc

import (
	"go.uber.org/zap"

	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage/backend"
	smvcc "go.etcd.io/etcd/server/v3/storage/mvcc"
)

// REQ mvcc/boot: a store opened over a storage that already holds a history (a restarting member's
// backend, or a fresh one) starts at that history's revision and compaction revision, resuming a
// compaction the storage recorded as unfinished; the keys' leases are re-attached to the lessor.
// Users: server/etcdserver/server.go:366 (mvcc.New over the bootstrapped backend, after
// lease.NewLessor), examples/mvccrand/mvccrand.go:811 (a fresh backend).
// Assumes: (reader tokens: two, from NewStore's) be holds an image of a history whose current
// revision is rev and compaction revision
// crev (−1: none) (the server's durable state: its last commit's image); le is a lessor over be;
// no hook is set yet.
// Specs: NewStore.spec (New.spec, 3f's, the same over the watchable store), store.Rev.spec,
// store.FirstRev.spec.
func ReqBoot(lg *zap.Logger, be backend.Backend, le lease.Lessor, rev, crev int64) smvcc.KV {
	kv := smvcc.NewStore(lg, be, le, smvcc.StoreConfig{})
	if kv.Rev() != rev || kv.FirstRev() != crev {
		panic("boot: the store is not at its storage's history")
	}
	return kv
}

// REQ mvcc/restore: a restore from a snapshot's storage leaves the store at the snapshot's
// history (never behind the store's), returns no error, and gives the old storage back (the
// server closes it).
// Users: server/etcdserver/server.go:1087-1098 (applySnapshot: lessor.Recover, kv.Restore, the new
// backend's hook set after it, the old backend closed).
// Assumes: (a reader token for the Rev) newbe holds an image of a history extending the store's, at
// revision rev (the server's
// snapshot is ahead of its applied index); the caller holds the open token and the whole store's
// storage share; le recovered over newbe (its item map empty).
// Specs: store.Restore.spec (KV.Restore.contract: storageRest of the old storage), store.Rev.spec.
func ReqRestore(kv smvcc.KV, oldbe, newbe backend.Backend, rev int64) {
	if err := kv.Restore(newbe); err != nil {
		panic("restore: a restore from a snapshot's backend failed")
	}
	if kv.Rev() != rev {
		panic("restore: the store is not at the snapshot's revision")
	}
	go oldbe.Close()
}

// REQ mvcc/close: the store closes once (its open token), and once every read is done the client
// may close the storage.
// Users: server/etcdserver/server.go:376 (NewServer's error path), 950 (Cleanup: kv.Close, then the
// backend's close), examples/mvccrand (after its checks).
// Assumes: no read of kv is in flight or will start (the caller holds every reader token).
// Specs: store.Close.spec (mvccClosed), mvccClosed_rest (the storage's rest back).
func ReqClose(kv smvcc.KV, be backend.Backend) {
	if err := kv.Close(); err != nil {
		panic("close: Close failed")
	}
	be.Close()
}
