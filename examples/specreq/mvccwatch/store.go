package mvccwatch

import (
	"context"

	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage/backend"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
)

// REQ mvccwatch/store-writes: the watchable store's writes (a write transaction's End, Put,
// DeleteRange) reach a watcher of the key in the order they commit, each once.
// Users: the apply path (server/etcdserver/txn: kv.Write and End), the lessor's revoke
// (lease/lessor.go:361 through the range deleter), the write view.
// Assumes: kv is a watchable store this snippet alone writes, never compacted.
// Specs: watchableStore.Write.spec, watchableStoreTxnWrite.Put.spec,
// watchableStoreTxnWrite.End.spec (the notify step: mvccLb's history gains the revision before the
// watchers are sent it), watchableStore.Put.spec; wsCons_recv.spec.
func ReqStoreWrites(kv mvcc.WatchableKV, k []byte) {
	ws := kv.NewWatchStream()
	defer ws.Close()
	id, err := ws.Watch(context.TODO(), 0, k, nil, 0)
	if err != nil {
		panic("store-writes: refused")
	}
	txn := kv.Write(traceutil.TODO())
	r1 := txn.Put(k, []byte("1"), lease.NoLease)
	txn.End()
	r2 := kv.Put(k, []byte("2"), lease.NoLease)
	got := recvEvents(ws, id, 2)
	if len(got) != 2 || got[0].Kv.ModRevision != r1 || got[1].Kv.ModRevision != r2 || r1 >= r2 {
		panic("store-writes: a write lost, repeated or reordered")
	}
}

// REQ mvccwatch/restore: after Restore from a storage holding a later point of the history, a
// watcher registered before keeps its position: it is sent the events after it, from the new
// storage, without repeating any.
// Users: EtcdServer.applySnapshot (server/etcdserver/server.go:1094: s.kv.Restore(newbe), then the
// watchers resync).
// Assumes: b holds an image of a history extending kv's (a snapshot from a later point of the
// cluster's history: the server's invariant), with its hook and commit resources; nothing pending
// (the caller is the apply thread); the restored store is not compacted past the watcher's position.
// Specs: watchableStore.Restore.spec (its update: the new history extends the old, histLe),
// wsCons_recv.spec (mvccLb's history grows past the restore).
func ReqRestore(kv mvcc.WatchableKV, b backend.Backend, k []byte) {
	ws := kv.NewWatchStream()
	defer ws.Close()
	rev0 := kv.Rev()
	id, err := ws.Watch(context.TODO(), 0, k, nil, rev0+1)
	if err != nil {
		panic("restore: refused")
	}
	if err := kv.Restore(b); err != nil {
		panic("restore: a valid snapshot's storage refused")
	}
	select {
	case resp := <-ws.Chan():
		if resp.WatchID != id {
			panic("restore: a foreign id")
		}
		for _, ev := range resp.Events {
			if ev.Kv.ModRevision <= rev0 {
				panic("restore: an event before the watcher's start after the restore")
			}
		}
	default:
	}
}

// REQ mvccwatch/close-store: Close stops the loops and closes the store, once (the server's
// cleanup closes the backend after it, with every reader token back).
// Users: EtcdServer.Cleanup (server/etcdserver/server.go:950).
// Assumes: the open token (called once).
// Specs: watchableStore.Close.spec (mvccClosed: the loops' readers back), 3e's mvccClosed_rest.
func ReqCloseStore(kv mvcc.WatchableKV) {
	if err := kv.Close(); err != nil {
		panic("close-store: an error")
	}
}
