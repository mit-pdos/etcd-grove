package mvccwatch

import (
	"context"

	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
)

// REQ mvccwatch/progress-one: a progress response of a watcher (no events, its id) is at a
// revision at least that of every event it was sent before, and at least its start: nothing of it
// was missed up to there.
// Users: v3rpc's sendLoop ticker (watch.go:594, RequestProgress for each watcher with progress
// notification); 1b's watchStep progress case.
// Assumes: kv is a watchable store this snippet alone writes, never compacted; one reader token.
// Specs: watchStream.RequestProgress.spec, watchStream.Watch.spec; wsCons_recv.spec (wStep's
// progStep at posOf).
func ReqProgressOne(kv mvcc.WatchableKV, k []byte) {
	ws := kv.NewWatchStream()
	defer ws.Close()
	id, err := ws.Watch(context.TODO(), 0, k, nil, 0)
	if err != nil {
		panic("progress-one: refused")
	}
	rev := kv.Put(k, []byte("v"), lease.NoLease)
	got := recvEvents(ws, id, 1)
	if got[0].Kv.ModRevision != rev {
		panic("progress-one: the event")
	}
	ws.RequestProgress(id)
	select {
	case resp := <-ws.Chan():
		if resp.WatchID != id || len(resp.Events) != 0 || resp.CompactRevision != 0 {
			panic("progress-one: not a progress of the watcher")
		}
		if resp.Revision < rev {
			panic("progress-one: a progress below an event already sent")
		}
	default:
		// the watcher may be unsynced (a victim): no progress then
	}
}

// REQ mvccwatch/progress-all: a stream-wide progress (id -1) covers every watcher registered
// before it and not cancelled: its revision is at least each one's last event and start.
// Users: v3rpc's recvLoop (watch.go:400, a progress request: RequestProgressAll under sws.mu);
// 1b's wireStep id -1 case.
// Assumes: as ReqProgressOne.
// Specs: watchStream.RequestProgressAll.spec, watchStream.Watch.spec (the stamp, wsSentLb);
// wsCons_recv.spec (the -1 case of wsRespOk).
func ReqProgressAll(kv mvcc.WatchableKV, k1, k2 []byte) {
	ws := kv.NewWatchStream()
	defer ws.Close()
	id1, err1 := ws.Watch(context.TODO(), 0, k1, nil, 0)
	id2, err2 := ws.Watch(context.TODO(), 0, k2, nil, 0)
	if err1 != nil || err2 != nil {
		panic("progress-all: refused")
	}
	r1 := kv.Put(k1, []byte("v"), lease.NoLease)
	recvEvents(ws, id1, 1)
	if ws.RequestProgressAll() {
		select {
		case resp := <-ws.Chan():
			if resp.WatchID != -1 && resp.WatchID != id1 && resp.WatchID != id2 {
				panic("progress-all: a foreign id")
			}
			if resp.WatchID == -1 && (len(resp.Events) != 0 || resp.Revision < r1) {
				panic("progress-all: a stream progress below a watcher's last event")
			}
		default:
		}
	}
}

// REQ mvccwatch/drain-before-created: after Watch returned, draining the channel without blocking
// until it is empty receives every response sent before the registration; a stream-wide progress
// received after the drain covers the new watcher (its revision is at least the store's revision
// before Watch).
// Users: v3rpc's sendLoop (watch.go:536: the drain before sending a Created; the fork's fix of
// issues/etcd-watch-progress-before-created.md).
// Assumes: kv is a watchable store this snippet alone writes, never compacted.
// Specs: watchStream.Watch.spec (wsSentLb of its stamp), wsCons_recv.spec (the non-blocking
// receive's empty case: the stamp is at most what was received), watchStream.RequestProgressAll.spec.
func ReqDrainBeforeCreated(kv mvcc.WatchableKV, k []byte) {
	ws := kv.NewWatchStream()
	defer ws.Close()
	rev0 := kv.Rev()
	id, err := ws.Watch(context.TODO(), 0, k, nil, 0)
	if err != nil {
		panic("drain: refused")
	}
	for drained := false; !drained; {
		select {
		case <-ws.Chan():
		default:
			drained = true
		}
	}
	if ws.RequestProgressAll() {
		select {
		case resp := <-ws.Chan():
			if resp.WatchID == -1 && resp.Revision < rev0 {
				panic("drain: a progress from before the registration read as covering it")
			}
			if resp.WatchID != -1 && resp.WatchID != id {
				panic("drain: a foreign id")
			}
		default:
		}
	}
}
