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
// Specs: watchStream.Watch.spec (n ≤ id, wsCtl ι (id + 1)), watchStream.Cancel.spec.
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
			if ws.Cancel(id) != nil {
				panic("fresh-ids: a live watcher's cancel failed")
			}
		}
	}
}

// REQ mvccwatch/empty-range: a watch of an empty range ([b, a)) is refused with -1 and an error
// with a message (v3rpc answers the create Canceled with it as the reason).
// Users: v3rpc's recvLoop (watch.go:342-364: id = -1, CancelReason = err.Error(), non-empty).
// Assumes: none but a reader token.
// Specs: watchStream.Watch.spec (the error disjunct, errMsgOk).
func ReqEmptyRange(kv mvcc.WatchableKV) {
	ws := kv.NewWatchStream()
	defer ws.Close()
	id, err := ws.Watch(context.TODO(), 0, []byte("b"), []byte("a"), 0)
	if err == nil || id != -1 {
		panic("empty-range: an empty range registered")
	}
	if err.Error() == "" {
		panic("empty-range: no reason to send")
	}
}

// REQ mvccwatch/cancel: after Cancel(id) returns nil, no response of the watcher is produced (those
// already queued may still arrive: none of them is of a write after the cancel).
// Users: v3rpc's recvLoop (watch.go:377: a cancel request; the cancel's answer retires the id).
// Assumes: kv is a watchable store this snippet alone writes, never compacted.
// Specs: watchStream.Cancel.spec (wsCanceled), wsCons_recv.spec (a response of a cancelled id is
// among the first c sent).
func ReqCancel(kv mvcc.WatchableKV, k, other []byte) {
	ws := kv.NewWatchStream()
	defer ws.Close()
	id, err := ws.Watch(context.TODO(), 0, k, nil, 0)
	id2, err2 := ws.Watch(context.TODO(), 0, other, nil, 0)
	if err != nil || err2 != nil {
		panic("cancel: refused")
	}
	if ws.Cancel(id) != nil {
		panic("cancel: a live watcher's cancel failed")
	}
	after := kv.Put(k, []byte("late"), lease.NoLease)
	kv.Put(other, []byte("x"), lease.NoLease)
	for {
		resp := <-ws.Chan()
		if resp.WatchID == id {
			for _, ev := range resp.Events {
				if ev.Kv.ModRevision >= after {
					panic("cancel: an event produced after the cancel")
				}
			}
		}
		if resp.WatchID == id2 && len(resp.Events) > 0 {
			return
		}
	}
}

// REQ mvccwatch/close: Close ends the stream: its channel closes after the queued responses;
// later Watch and Cancel fail; later RequestProgress and RequestProgressAll send nothing (no send
// on the closed channel: v3rpc's receive loop may still call them).
// Users: v3rpc's serverWatchStream.close (watch.go:668), the receive loop after it (watchServer.Watch's
// context branch).
// Assumes: one reader token; Close called once.
// Specs: watchStream.Close.spec (wsOpen spent, wsClosed), watchStream.Watch.spec (the error
// disjunct), watchStream.Cancel.spec, watchStream.RequestProgress.spec,
// watchStream.RequestProgressAll.spec, wsCons_recv.spec (!ok).
func ReqClose(kv mvcc.WatchableKV, k []byte) {
	ws := kv.NewWatchStream()
	id, err := ws.Watch(context.TODO(), 0, k, nil, 0)
	if err != nil {
		panic("close: refused")
	}
	ws.Close()
	if _, err := ws.Watch(context.TODO(), 0, k, nil, 0); err == nil {
		panic("close: a watch on a closed stream")
	}
	if ws.Cancel(id) == nil {
		panic("close: a cancel on a closed stream")
	}
	ws.RequestProgress(id)
	ws.RequestProgressAll()
	for range ws.Chan() {
	}
}
