// Package mvccwatch holds the requirement snippets of mvcc's watch API (batch 3f): what its users
// (etcd's gRPC watch handler, v3rpc's serverWatchStream, and the server that owns the store)
// rely on of a watch stream of the watchable store.
package mvccwatch

import (
	"context"

	"go.etcd.io/etcd/api/v3/mvccpb"
	"go.etcd.io/etcd/pkg/v3/traceutil"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
)

// recvEvents receives from the stream until n events of the watcher id arrived; a stream-wide
// progress (id -1) is skipped; any other response of id is a progress (no events: skipped; mvcc may send one unrequested only through a
// RequestProgress, but the specs admit it at any time) or a compaction (which the snippets'
// assumptions rule out). The stream's only watcher is id (wsReg_ctl: a registered id is one Watch
// returned).

// nextNonProgress receives the next response that is not a progress of a watcher.
func nextNonProgress(ws mvcc.WatchStream) mvcc.WatchResponse {
	for {
		resp, ok := <-ws.Chan()
		if !ok {
			panic("history: channel closed while the stream is open")
		}
		if len(resp.Events) == 0 && resp.CompactRevision == 0 {
			continue
		}
		return resp
	}
}

func recvEvents(ws mvcc.WatchStream, id mvcc.WatchID, n int) []*mvccpb.Event {
	var got []*mvccpb.Event
	for len(got) < n {
		resp, ok := <-ws.Chan()
		if !ok {
			panic("history: channel closed while the stream is open")
		}
		if resp.WatchID == -1 {
			// A stream-wide progress: wsRespOk admits one at any time (only RequestProgressAll
			// sends one, which no spec says), so it is skipped, as nextNonProgress does.
			continue
		}
		if resp.WatchID != id {
			panic("history: a response of a watcher this stream does not have")
		}
		if resp.CompactRevision != 0 {
			panic("history: compacted, though no compaction ran")
		}
		for _, ev := range resp.Events {
			if ev.Kv.ModRevision > resp.Revision {
				panic("history: an event above its response's revision")
			}
		}
		got = append(got, resp.Events...)
	}
	return got
}

// REQ mvccwatch/from-start: a watcher from a start revision receives exactly its range's events
// from that revision on, in revision order, without a gap; a delete event carries its key and its
// revision.
// Users: server/etcdserver/api/v3rpc/watch.go:342 (recvLoop's Watch with the create's start
// revision), watch.go:516 (sendLoop forwards each response).
// Assumes: kv is a watchable store this snippet alone writes (the server's apply thread is the
// only writer: its invariant holds mvccState) and never compacts; one reader token.
// Specs: watchableStore.Rev.spec, watchableStore.NewWatchStream.spec, watchStream.Watch.spec (+ wsOpen_closed) (id = n,
// the read update), wsReg_ctl,
// watchableStore.Put.spec, watchableStore.DeleteRange.spec, watchStream.Close.spec; laws:
// wsCons_recv.spec (wStep's events: wEvents of the range from the position), mvccLb_le.spec.
func ReqFromStart(kv mvcc.WatchableKV, k []byte) {
	rev0 := kv.Rev()
	ws := kv.NewWatchStream()
	defer ws.Close()
	id, err := ws.Watch(context.TODO(), 0, k, nil, rev0+1)
	if err != nil || id == -1 {
		panic("from-start: a valid watch refused")
	}
	kv.Put(k, []byte("a"), lease.NoLease)
	kv.Put([]byte("other"), []byte("x"), lease.NoLease)
	kv.DeleteRange(k, nil)
	got := recvEvents(ws, id, 2)
	if len(got) != 2 {
		panic("from-start: an event of another key, or one too many")
	}
	if got[0].Type != mvccpb.PUT || string(got[0].Kv.Value) != "a" || got[0].Kv.ModRevision != rev0+1 {
		panic("from-start: the first change lost")
	}
	if got[1].Type != mvccpb.DELETE || string(got[1].Kv.Key) != string(k) || got[1].Kv.ModRevision != rev0+3 {
		panic("from-start: the delete lost or misplaced")
	}
	if got[0].PrevKv != nil {
		panic("from-start: mvcc fills no previous key-value")
	}
}

// REQ mvccwatch/from-current: a watcher from revision 0 receives every event after the store's
// revision at its registration, which is at most a revision Rev() reports after Watch returned.
// Users: v3rpc's recvLoop (a create with start revision 0, its Created header from Rev()).
// Assumes: as ReqFromStart.
// Specs: watchStream.Watch.spec (+ wsOpen_closed) (W.pos = σ.rev at the state its read update fired),
// watchStream.Rev.spec (its read update at a later state: the snippet's state only grows);
// wsCons_recv.spec.
func ReqFromCurrent(kv mvcc.WatchableKV, k []byte) {
	ws := kv.NewWatchStream()
	defer ws.Close()
	id, err := ws.Watch(context.TODO(), 0, k, nil, 0)
	if err != nil {
		panic("from-current: refused")
	}
	r := ws.Rev()
	rev := kv.Put(k, []byte("v"), lease.NoLease)
	if rev <= r {
		panic("from-current: a write after Rev() at or below it")
	}
	got := recvEvents(ws, id, 1)
	if got[0].Kv.ModRevision != rev {
		panic("from-current: the write after registration missed")
	}
}

// REQ mvccwatch/whole-revision: all of a revision's events in a watcher's range come in one
// response (a transaction's puts are not split).
// Users: v3rpc's sendLoop (one gRPC response per mvcc response; 1b's wireStep: whole revisions).
// Assumes: as ReqFromStart.
// Specs: watchableStore.Write.spec, watchableStoreTxnWrite.Put.spec, watchableStoreTxnWrite.End.spec,
// watchStream.Watch.spec (+ wsOpen_closed); wsCons_recv.spec (wEvents up to the last event's revision).
func ReqWholeRevision(kv mvcc.WatchableKV) {
	ws := kv.NewWatchStream()
	defer ws.Close()
	id, err := ws.Watch(context.TODO(), 0, []byte("a"), []byte{}, 0)
	if err != nil {
		panic("whole-revision: refused")
	}
	txn := kv.Write(traceutil.TODO())
	txn.Put([]byte("a1"), []byte("x"), lease.NoLease)
	txn.Put([]byte("a2"), []byte("y"), lease.NoLease)
	txn.End()
	resp := nextNonProgress(ws)
	if resp.WatchID != id || len(resp.Events) != 2 {
		panic("whole-revision: a revision split across responses")
	}
}

// REQ mvccwatch/filters: a filter that drops puts leaves only the deletes; a response whose
// events were all dropped is not sent.
// Users: v3rpc's FiltersFromRequest (NOPUT, NODELETE) passed to Watch (watch.go:338-342).
// Assumes: as ReqFromStart.
// Specs: watchStream.Watch.spec (+ wsOpen_closed) with filtersAt (filterOk of the function); wsCons_recv.spec.
func ReqFilters(kv mvcc.WatchableKV, k []byte) {
	noPut := func(e *mvccpb.Event) bool { return e.Type == mvccpb.PUT }
	ws := kv.NewWatchStream()
	defer ws.Close()
	id, err := ws.Watch(context.TODO(), 0, k, nil, 0, noPut)
	if err != nil {
		panic("filters: refused")
	}
	kv.Put(k, []byte("v"), lease.NoLease)
	_, rev := kv.DeleteRange(k, nil)
	resp := nextNonProgress(ws)
	if resp.WatchID != id || len(resp.Events) != 1 || resp.Events[0].Type != mvccpb.DELETE ||
		resp.Events[0].Kv.ModRevision != rev {
		panic("filters: a filtered put delivered, or an empty response sent")
	}
}

// REQ mvccwatch/compaction: a watcher from below the store's compaction revision gets one
// compaction response (its revision 0, no events, the compaction revision above its start) and no
// event.
// Users: v3rpc's sendLoop (Canceled iff CompactRevision != 0; 1b's watchStep error arm).
// Assumes: kv is written and compacted by this snippet alone; at least two revisions written
// before (so that the compaction revision exceeds the start 1).
// Specs: watchableStore.Compact.spec, watchStream.Watch.spec (+ wsOpen_closed); wsCons_recv.spec (wStep's
// compaction case against posEvOf, respShape).
func ReqCompaction(kv mvcc.WatchableKV, k []byte) {
	kv.Put(k, []byte("a"), lease.NoLease)
	rev := kv.Put(k, []byte("b"), lease.NoLease)
	if _, err := kv.Compact(traceutil.TODO(), rev); err != nil {
		panic("compaction: a valid compaction refused")
	}
	ws := kv.NewWatchStream()
	defer ws.Close()
	id, err := ws.Watch(context.TODO(), 0, k, nil, 1)
	if err != nil {
		panic("compaction: refused")
	}
	resp := nextNonProgress(ws)
	if resp.WatchID != id || resp.CompactRevision == 0 || len(resp.Events) != 0 || resp.Revision != 0 {
		panic("compaction: events from below the compaction")
	}
	if resp.CompactRevision <= 1 || resp.CompactRevision > rev {
		panic("compaction: a compaction revision the store never had")
	}
}
