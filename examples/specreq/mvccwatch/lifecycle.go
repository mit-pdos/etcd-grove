package mvccwatch

import (
	"context"

	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
)

// REQ mvccwatch/fresh-ids: the ids a stream's Watch returns are never -1 and never repeat.
// Users: v3rpc's recvLoop (a Created carries the id; 1b's wireStep: an announced id is fresh,
// WireSt.seen; -1 is the stream-wide id).
// Assumes: one reader token; the control side is this goroutine.
// Specs: watchStream.Watch.spec (id = n, wsCtl ι (n + 1)), watchStream.Cancel.spec.
func ReqFreshIds(kv mvcc.WatchableKV, k []byte) {
	ws := kv.NewWatchStream()
	defer ws.Close()
	seen := map[mvcc.WatchID]bool{}
	for i := 0; i < 3; i++ {
		id, err := ws.Watch(context.TODO(), 0, k, nil, 0)
		if err != nil {
			panic("fresh-ids: refused")
		}
		if id == -1 || seen[id] {
			panic("fresh-ids: an id reused or -1")
		}
		seen[id] = true
		if i == 1 {
			_ = ws.Cancel(id) // either way, the next id is fresh
		}
	}
}

// REQ mvccwatch/empty-range: a watch of an empty range ([b, a)) is refused with -1 and an error
// with a message (v3rpc answers the create Canceled with it as the reason).
// Users: v3rpc's recvLoop (watch.go:342-364: id = -1, CancelReason = err.Error(), non-empty).
// Assumes: none but a reader token.
// Specs: watchStream.Watch.spec (the error disjunct: the package's ErrEmptyWatcherRange; its
// success disjunct excludes an empty range), watch_init.spec (its message).
func ReqEmptyRange(kv mvcc.WatchableKV) {
	ws := kv.NewWatchStream()
	defer ws.Close()
	id, err := ws.Watch(context.TODO(), 0, []byte("b"), []byte("a"), 0)
	if err == nil || id != -1 {
		panic("empty-range: an empty range registered")
	}
	if err != mvcc.ErrEmptyWatcherRange {
		panic("empty-range: not the package's error (examples/mvccrand compares it)")
	}
	if err.Error() == "" {
		panic("empty-range: no reason to send")
	}
}

// REQ mvccwatch/cancel: Cancel of a registered watcher returns nil (then the watcher is
// cancelled: no response of it after the sends so far, which v3rpc does not rely on: it retires
// the id itself) or the package's ErrWatcherNotExist; a cancel of an id never registered fails.
// Users: v3rpc's recvLoop (watch.go:377: a cancel request; nil answers it, an error does not).
// Assumes: none but the stream.
// Specs: watchStream.Cancel.spec (nil gives wsReg of the id: an id never registered is not
// cancelled, wsReg_ctl), watchStream.Watch.spec.
func ReqCancel(kv mvcc.WatchableKV, k, other []byte) {
	ws := kv.NewWatchStream()
	defer ws.Close()
	id, err := ws.Watch(context.TODO(), 0, k, nil, 0)
	if err != nil {
		panic("cancel: refused")
	}
	if err := ws.Cancel(id); err != nil && err != mvcc.ErrWatcherNotExist {
		panic("cancel: an error that is not the package's")
	}
	if ws.Cancel(id+1) == nil {
		panic("cancel: an id never registered cancelled")
	}
	_ = other
	_ = lease.NoLease
}

// REQ mvccwatch/close: Close ends the stream: its channel closes after the queued responses;
// later RequestProgress and RequestProgressAll do not panic (no send on the closed channel:
// v3rpc's receive loop may still call them). (That a later Watch or Cancel fails is true of the
// code, not given by the specs: no caller relies on it.)
// Users: v3rpc's serverWatchStream.close (watch.go:668), the receive loop after it (watchServer.Watch's
// context branch).
// Assumes: one reader token; Close called once.
// Specs: watchStream.Close.spec (wsOpen spent, wsClosed), watchStream.RequestProgress.spec,
// watchStream.RequestProgressAll.spec, wsCons_recv.spec (!ok).
func ReqClose(kv mvcc.WatchableKV, k []byte) {
	ws := kv.NewWatchStream()
	id, err := ws.Watch(context.TODO(), 0, k, nil, 0)
	if err != nil {
		panic("close: refused")
	}
	ws.Close()
	ws.RequestProgress(id)
	ws.RequestProgressAll()
	for range ws.Chan() {
	}
}
