// Package v3rpcwatch holds the requirement snippets of etcd's gRPC watch service (batch 2b,
// Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/ApiWatch.lean): what a client of a member's
// Watch stream relies on, over a raw pb.WatchClient stream, as the Go client's watchGRPCStream
// (client/v3/watch.go: run, serveWatchClient, dispatchEvent, serveSubstream) does, each reliance an
// explicit panic.
//
// Common assumptions: wc is a pb.WatchClient and kc a pb.KVClient of a member of a cluster
// (1b's remoteWatchAt, W0's remoteKVAt, over 2a's servesAt); the caller owns the cluster's state in
// an invariant of its own (the "owner's invariant"); a key a snippet names as "owned" is written by
// no other principal and attached to no lease; no compaction unless the snippet compacts; requests
// are sent as the Go client sends them (WatchId 0, a non-nil oneof: the wire model, 1b's
// WireWatchReq). Errors the client handles (a failed Send or Recv, a failed KV call) are handled as
// it does: return.
package v3rpcwatch

import (
	"context"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/mvccpb"
)

func create(key, end []byte, rev int64, prevKV, fragment bool) *pb.WatchRequest {
	return &pb.WatchRequest{RequestUnion: &pb.WatchRequest_CreateRequest{
		CreateRequest: &pb.WatchCreateRequest{Key: key, RangeEnd: end, StartRevision: rev,
			PrevKv: prevKV, Fragment: fragment}}}
}

func progress() *pb.WatchRequest {
	return &pb.WatchRequest{RequestUnion: &pb.WatchRequest_ProgressRequest{
		ProgressRequest: &pb.WatchProgressRequest{}}}
}

func cancel(id int64) *pb.WatchRequest {
	return &pb.WatchRequest{RequestUnion: &pb.WatchRequest_CancelRequest{
		CancelRequest: &pb.WatchCancelRequest{WatchId: id}}}
}

// recvCreated receives up to the next Created response (skipping others), or fails.
func recvCreated(ws pb.Watch_WatchClient) (*pb.WatchResponse, bool) {
	for {
		r, err := ws.Recv()
		if err != nil {
			return nil, false
		}
		if r.Created {
			return r, true
		}
	}
}

// REQ v3rpcwatch/creates-in-order: the k-th Created answers the k-th create; a registered watch has
// an id other than -1, fresh on the stream; a refused one has id -1 and a reason.
// Users: client/v3/watch.go:605 (run: a Created answers the head of `resuming`), :468
// (addSubstream: WatchId -1 or a reason means refused), :1081 (toPB: WatchId 0).
// Assumes: the common assumptions.
// Specs: watchServer.Watch.spec (WatchServer.WatchTriple through 2a's registration); srvWireStep's
// Created cases (creates answered FIFO, `st.reg id = none`, `id ≠ -1`, `cancelReason ≠ []`).
func ReqCreatesInOrder(ctx context.Context, wc pb.WatchClient, k1, k2 []byte) {
	ws, err := wc.Watch(ctx)
	if err != nil {
		return
	}
	if ws.Send(create(k1, nil, 0, false, false)) != nil || ws.Send(create(k2, nil, -1, false, false)) != nil {
		return
	}
	r1, ok := recvCreated(ws)
	if !ok {
		return
	}
	r2, ok := recvCreated(ws)
	if !ok {
		return
	}
	// The second create (a negative start revision) is refused; the first is not.
	if r1.Canceled || r1.WatchId == -1 {
		panic("creates-in-order: the first create is registered, with an id")
	}
	if !r2.Canceled || r2.WatchId != -1 || r2.CancelReason == "" {
		panic("creates-in-order: the second create is refused, id -1, with a reason")
	}
}

// REQ v3rpcwatch/from-start: a watch from revision r delivers the range's events from r on, in
// order, every event of a revision in one response, with the header at least the last event's.
// Users: client/v3/watch.go:849 (serveSubstream: events advance the resume revision past the last
// one), Kubernetes' etcd3 watcher and the cache through the client (1b's clientv3watch/history.go).
// Assumes: k is owned; nothing compacts.
// Specs: srvWireStep (watchStep's event case at WatchPos.init r), kv's Put (W0).
func ReqFromStart(ctx context.Context, wc pb.WatchClient, kc pb.KVClient, k []byte) {
	p1, err := kc.Put(ctx, &pb.PutRequest{Key: k, Value: []byte("1")})
	if err != nil {
		return
	}
	p2, err := kc.Put(ctx, &pb.PutRequest{Key: k, Value: []byte("2")})
	if err != nil {
		return
	}
	ws, err := wc.Watch(ctx)
	if err != nil || ws.Send(create(k, nil, p1.Header.Revision, false, false)) != nil {
		return
	}
	c, ok := recvCreated(ws)
	if !ok || c.Canceled {
		return
	}
	var evs []*mvccpb.Event
	for len(evs) < 2 {
		r, err := ws.Recv()
		if err != nil {
			return
		}
		if r.WatchId != c.WatchId || len(r.Events) == 0 {
			continue
		}
		if r.Header.Revision < r.Events[len(r.Events)-1].Kv.ModRevision {
			panic("from-start: the header is at least the last event's revision")
		}
		evs = append(evs, r.Events...)
	}
	if evs[0].Kv.ModRevision != p1.Header.Revision || string(evs[0].Kv.Value) != "1" ||
		evs[1].Kv.ModRevision != p2.Header.Revision || string(evs[1].Kv.Value) != "2" {
		panic("from-start: the two puts, in order, from the start revision")
	}
}

// REQ v3rpcwatch/whole-revision: the events of one revision (a transaction's) come in one
// response.
// Users: Kubernetes' etcd3 watcher (a transaction's events, through the client), the cache's
// progress (cache/watch.go: a revision is complete when its response arrives).
// Assumes: the prefix pfx is owned; nothing compacts; pfx+"\xff" is pfx's range end.
// Specs: srvWireStep (watchStep's event case: `watchEvents w σ.kv lo c'` with `c'` the last
// event's revision: every event of revisions up to c').
func ReqWholeRevision(ctx context.Context, wc pb.WatchClient, kc pb.KVClient, pfx string) {
	t, err := kc.Txn(ctx, &pb.TxnRequest{Success: []*pb.RequestOp{
		{Request: &pb.RequestOp_RequestPut{RequestPut: &pb.PutRequest{Key: []byte(pfx + "a"), Value: []byte("1")}}},
		{Request: &pb.RequestOp_RequestPut{RequestPut: &pb.PutRequest{Key: []byte(pfx + "b"), Value: []byte("1")}}},
	}})
	if err != nil || !t.Succeeded {
		return
	}
	ws, err := wc.Watch(ctx)
	if err != nil || ws.Send(create([]byte(pfx), []byte(pfx+"\xff"), t.Header.Revision, false, false)) != nil {
		return
	}
	c, ok := recvCreated(ws)
	if !ok || c.Canceled {
		return
	}
	for {
		r, err := ws.Recv()
		if err != nil {
			return
		}
		if r.WatchId != c.WatchId || len(r.Events) == 0 {
			continue
		}
		if len(r.Events) != 2 {
			panic("whole-revision: both puts of the transaction in one response")
		}
		return
	}
}

// REQ v3rpcwatch/progress: a progress notification of id -1 at revision P (after the watch's
// Created) means the watch missed nothing up to P: its next event is above P.
// Users: client/v3/watch.go:748 (dispatchEvent broadcasts a progress of id -1 to every substream),
// the cache's and Kubernetes' RequestProgress (a progress revision served as read freshness).
// Assumes: k is owned; nothing compacts.
// Specs: srvWireStep's id -1 case (every registration whose cancel was not received: no event in
// (done, P], done ≤ P).
func ReqProgress(ctx context.Context, wc pb.WatchClient, kc pb.KVClient, k []byte) {
	p0, err := kc.Put(ctx, &pb.PutRequest{Key: k, Value: []byte("0")})
	if err != nil {
		return
	}
	ws, err := wc.Watch(ctx)
	if err != nil || ws.Send(create(k, nil, p0.Header.Revision+1, false, false)) != nil {
		return
	}
	c, ok := recvCreated(ws)
	if !ok || c.Canceled {
		return
	}
	if ws.Send(progress()) != nil {
		return
	}
	var P int64 = -1
	for P < 0 {
		r, err := ws.Recv()
		if err != nil {
			return
		}
		if r.WatchId == c.WatchId && len(r.Events) > 0 {
			panic("progress: nothing was written to k after the watch's start")
		}
		if r.WatchId == -1 && len(r.Events) == 0 && !r.Created && !r.Canceled {
			P = r.Header.Revision
		}
	}
	p1, err := kc.Put(ctx, &pb.PutRequest{Key: k, Value: []byte("1")})
	if err != nil {
		return
	}
	for {
		r, err := ws.Recv()
		if err != nil {
			return
		}
		if r.WatchId == c.WatchId && len(r.Events) > 0 {
			if r.Events[0].Kv.ModRevision <= P || r.Events[0].Kv.ModRevision != p1.Header.Revision {
				panic("progress: the next event is above the progress revision")
			}
			return
		}
	}
}

// REQ v3rpcwatch/cancel: after the cancel response of an id, the stream carries nothing more of it.
// Users: client/v3/watch.go:625 (run: a cancel response closes the substream's recvc, after which
// nothing may be sent to it), :663 and :706 (cancel requests).
// Assumes: k is owned; nothing compacts.
// Specs: srvWireStep's cancel case (the registration removed; a later response of the id is
// "nothing") and the server's: no response of a canceled id is sent after its cancel response
// (the send loop's `ids`).
func ReqCancel(ctx context.Context, wc pb.WatchClient, kc pb.KVClient, k []byte) {
	ws, err := wc.Watch(ctx)
	if err != nil || ws.Send(create(k, nil, 0, false, false)) != nil {
		return
	}
	c, ok := recvCreated(ws)
	if !ok || c.Canceled {
		return
	}
	if ws.Send(cancel(c.WatchId)) != nil {
		return
	}
	for {
		r, err := ws.Recv()
		if err != nil {
			return
		}
		if r.WatchId == c.WatchId && r.Canceled && r.CompactRevision == 0 {
			break
		}
	}
	if _, err := kc.Put(ctx, &pb.PutRequest{Key: k, Value: []byte("1")}); err != nil {
		return
	}
	if ws.Send(create(k, nil, 0, false, false)) != nil {
		return
	}
	for {
		r, err := ws.Recv()
		if err != nil {
			return
		}
		if r.Created {
			if r.WatchId == c.WatchId {
				panic("cancel: a canceled id is not reused on the stream")
			}
			return
		}
		if r.WatchId == c.WatchId {
			panic("cancel: nothing of the id after its cancel response")
		}
	}
}

// REQ v3rpcwatch/compaction: a watch from a compacted revision gets its events from that revision
// (a member that has not applied the compaction) or one compaction response, canceled, without
// events, its compaction revision above the start and at most the cluster's compaction.
// Users: client/v3/watch.go:127 (WatchResponse.Err: ErrCompacted), Kubernetes' etcd3 watcher
// (relist on a compacted watch), the cache.
// Assumes: k is owned; only this snippet compacts.
// Specs: srvWireStep (watchStep's compaction case: `cr ≤ σ.kv.compacted`, `done + 1 < cr`), kv's
// Compact (W0).
func ReqCompaction(ctx context.Context, wc pb.WatchClient, kc pb.KVClient, k []byte) {
	p1, err := kc.Put(ctx, &pb.PutRequest{Key: k, Value: []byte("1")})
	if err != nil {
		return
	}
	p2, err := kc.Put(ctx, &pb.PutRequest{Key: k, Value: []byte("2")})
	if err != nil {
		return
	}
	if _, err := kc.Compact(ctx, &pb.CompactionRequest{Revision: p2.Header.Revision}); err != nil {
		return
	}
	ws, err := wc.Watch(ctx)
	if err != nil || ws.Send(create(k, nil, p1.Header.Revision, false, false)) != nil {
		return
	}
	c, ok := recvCreated(ws)
	if !ok || c.Canceled {
		return
	}
	for {
		r, err := ws.Recv()
		if err != nil {
			return
		}
		if r.WatchId != c.WatchId {
			continue
		}
		if r.CompactRevision != 0 {
			if !r.Canceled || len(r.Events) != 0 || r.CompactRevision <= p1.Header.Revision ||
				r.CompactRevision > p2.Header.Revision {
				panic("compaction: canceled, no events, above the start, at most the compaction")
			}
			return
		}
		if len(r.Events) > 0 {
			if r.Events[0].Kv.ModRevision != p1.Header.Revision {
				panic("compaction: events, if any, from the start revision")
			}
			return
		}
	}
}

// REQ v3rpcwatch/prev-kv: with PrevKv, an update's event carries the key's previous record.
// Users: Kubernetes' etcd3 watcher (WithPrevKV: the previous object of an update or delete),
// client/v3/leasing (prevKV of deletes, through the client).
// Assumes: k is owned; nothing compacts.
// Specs: srvWireStep (EventM.isOf: WatchReq.prevOk, the history's record at the revision before).
func ReqPrevKV(ctx context.Context, wc pb.WatchClient, kc pb.KVClient, k []byte) {
	if _, err := kc.Put(ctx, &pb.PutRequest{Key: k, Value: []byte("1")}); err != nil {
		return
	}
	p2, err := kc.Put(ctx, &pb.PutRequest{Key: k, Value: []byte("2")})
	if err != nil {
		return
	}
	ws, err := wc.Watch(ctx)
	if err != nil || ws.Send(create(k, nil, p2.Header.Revision, true, false)) != nil {
		return
	}
	c, ok := recvCreated(ws)
	if !ok || c.Canceled {
		return
	}
	for {
		r, err := ws.Recv()
		if err != nil {
			return
		}
		if r.WatchId != c.WatchId || len(r.Events) == 0 {
			continue
		}
		ev := r.Events[0]
		if ev.PrevKv == nil || string(ev.PrevKv.Value) != "1" {
			panic("prev-kv: the update's previous value")
		}
		return
	}
}

// REQ v3rpcwatch/fragments: the fragments of a response come contiguously, all of its id, neither
// a creation nor a cancel, the last without Fragment; reassembled, they are one response.
// Users: client/v3/watch.go:596-603 and :642 (run merges fragments into `cur` until one without
// Fragment).
// Assumes: the prefix pfx is owned; nothing compacts; pfx+"\xff" is pfx's range end.
// Specs: srvWireStep (the pending fragment's conjunct, the fragment case), sendFragments.spec.
func ReqFragments(ctx context.Context, wc pb.WatchClient, kc pb.KVClient, pfx string) {
	ws, err := wc.Watch(ctx)
	if err != nil || ws.Send(create([]byte(pfx), []byte(pfx+"\xff"), 0, false, true)) != nil {
		return
	}
	c, ok := recvCreated(ws)
	if !ok || c.Canceled {
		return
	}
	big := make([]byte, 1<<20)
	t, err := kc.Txn(ctx, &pb.TxnRequest{Success: []*pb.RequestOp{
		{Request: &pb.RequestOp_RequestPut{RequestPut: &pb.PutRequest{Key: []byte(pfx + "a"), Value: big}}},
		{Request: &pb.RequestOp_RequestPut{RequestPut: &pb.PutRequest{Key: []byte(pfx + "b"), Value: big}}},
	}})
	if err != nil || !t.Succeeded {
		return
	}
	var evs []*mvccpb.Event
	inFrag := false
	for {
		r, err := ws.Recv()
		if err != nil {
			return
		}
		if inFrag && (r.WatchId != c.WatchId || r.Created || r.Canceled) {
			panic("fragments: contiguous, of one id")
		}
		if r.WatchId != c.WatchId {
			continue
		}
		evs = append(evs, r.Events...)
		inFrag = r.Fragment
		if !inFrag && len(evs) > 0 {
			if len(evs) != 2 || evs[0].Kv.ModRevision != t.Header.Revision ||
				evs[1].Kv.ModRevision != t.Header.Revision {
				panic("fragments: reassembled, the transaction's two events")
			}
			return
		}
	}
}

// REQ v3rpcwatch/permission: with auth on, a watch on a range the principal may not read is
// refused (Created, Canceled, id -1).
// Users: client/v3/watch.go:468 (addSubstream: a refused watch's channel gets the cancel reason),
// examples/etcd/auth (a user's watch on another's prefix).
// Assumes: wc's principal (its context's token, W0's ctxPrin) is a user that holds no read
// permission on k at any state the cluster reaches and has not the root role (the owner's
// invariant: no grant of it), and auth is enabled at every reachable state.
// Specs: srvWireStep's registered-Created case (`σa.permits who [(.read, w.range)] []` at a reached
// σa), isWatchPermitted.spec.
func ReqPermission(ctx context.Context, wc pb.WatchClient, k []byte) {
	ws, err := wc.Watch(ctx)
	if err != nil || ws.Send(create(k, nil, 0, false, false)) != nil {
		return
	}
	c, ok := recvCreated(ws)
	if !ok {
		return
	}
	if !c.Canceled || c.WatchId != -1 {
		panic("permission: a watch the principal may not read is refused")
	}
}
