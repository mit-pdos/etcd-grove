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

func createWith(c *pb.WatchCreateRequest) *pb.WatchRequest {
	return &pb.WatchRequest{RequestUnion: &pb.WatchRequest_CreateRequest{CreateRequest: c}}
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

// REQ v3rpcwatch/creates-in-order: the k-th Created answers the k-th create; a create with a
// negative start revision is refused (id -1, a reason); a registered watch has an id other than -1,
// never announced before on the stream.
// Users: client/v3/watch.go:605 (run: a Created answers the head of `resuming`), :468
// (addSubstream: WatchId -1 or a reason means refused), :1081 (toPB: WatchId 0); raw tests
// (tests/integration/clientv3/watch: TestV3WatchWrongRange).
// Assumes: the common assumptions.
// Specs: watchServer.Watch.spec (WatchServer.WatchTriple through 2a's registration); wireStep's
// Created cases (creates answered FIFO, `s < 0 → canceled`, `id ∉ seen`, `id ≠ -1`,
// `cancelReason ≠ []`).
func ReqCreatesInOrder(ctx context.Context, wc pb.WatchClient, k1, k2 []byte) {
	ws, err := wc.Watch(ctx)
	if err != nil {
		return
	}
	if ws.Send(create(k1, nil, 0, false, false)) != nil || ws.Send(create(k2, nil, -1, false, false)) != nil ||
		ws.Send(create(k2, nil, 0, false, false)) != nil {
		return
	}
	var rs [3]*pb.WatchResponse
	for i := range rs {
		r, ok := recvCreated(ws)
		if !ok {
			return
		}
		rs[i] = r
	}
	if !rs[1].Canceled || rs[1].WatchId != -1 || rs[1].CancelReason == "" {
		panic("creates-in-order: the second create (negative start) is refused, id -1, with a reason")
	}
	for _, r := range []*pb.WatchResponse{rs[0], rs[2]} {
		if !r.Canceled && r.WatchId == -1 {
			panic("creates-in-order: a registered watch's id is not -1")
		}
	}
	if !rs[0].Canceled && !rs[2].Canceled && rs[0].WatchId == rs[2].WatchId {
		panic("creates-in-order: two registered watches have different ids")
	}
}

// REQ v3rpcwatch/two-watches: two live watches on one stream are told apart by id: each id's
// events are of its own range.
// Users: client/v3/watch.go:767-777 (unicastResponse routes by id to the substream), raw tests
// (tests/integration/clientv3/watch: several watches on one stream).
// Assumes: k1 and k2 are owned, distinct keys; nothing compacts.
// Specs: wireStep (a response of an id is a watchStep of that id's registration: `watchEvents` of
// its range).
func ReqTwoWatches(ctx context.Context, wc pb.WatchClient, kc pb.KVClient, k1, k2 []byte) {
	ws, err := wc.Watch(ctx)
	if err != nil || ws.Send(create(k1, nil, 0, false, false)) != nil || ws.Send(create(k2, nil, 0, false, false)) != nil {
		return
	}
	c1, ok := recvCreated(ws)
	if !ok || c1.Canceled {
		return
	}
	c2, ok := recvCreated(ws)
	if !ok || c2.Canceled {
		return
	}
	if _, err := kc.Put(ctx, &pb.PutRequest{Key: k2, Value: []byte("2")}); err != nil {
		return
	}
	if _, err := kc.Put(ctx, &pb.PutRequest{Key: k1, Value: []byte("1")}); err != nil {
		return
	}
	for seen := 0; seen < 2; {
		r, err := ws.Recv()
		if err != nil {
			return
		}
		for _, ev := range r.Events {
			if (r.WatchId == c1.WatchId && string(ev.Kv.Key) != string(k1)) ||
				(r.WatchId == c2.WatchId && string(ev.Kv.Key) != string(k2)) {
				panic("two-watches: each id's events are of its own key")
			}
		}
		if len(r.Events) > 0 {
			seen++
		}
	}
}

// REQ v3rpcwatch/from-start: a watch from revision r delivers the range's events from r on, in
// order, every event of a revision in one response, with the header at least the last event's.
// Users: client/v3/watch.go:849 (serveSubstream: events advance the resume revision past the last
// one), Kubernetes' etcd3 watcher and the cache through the client (1b's clientv3watch/history.go).
// Assumes: k is owned; nothing compacts.
// Specs: wireStep (watchStep's event case at WatchPos.init r; fragments only for a watch created
// with Fragment), kv's Put (W0).
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
		if r.Fragment {
			panic("from-start: no fragments for a watch that did not ask for them")
		}
		if r.GetHeader().GetRevision() < r.Events[len(r.Events)-1].Kv.ModRevision {
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
// Specs: wireStep (watchStep's event case: `watchEvents w σ.kv lo c'` with `c'` the last
// event's revision: every event of revisions up to c'; no fragment of a watch created without
// Fragment).
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
// Specs: wireStep's id -1 case (every registration whose cancel was not received: no event in
// (done, P], done ≤ P; every response has a header; no fragment of id -1).
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
		if r.WatchId == -1 && len(r.Events) == 0 && !r.Created && !r.Canceled && !r.Fragment {
			if r.Header == nil {
				panic("progress: every response has a header")
			}
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
// Specs: wireStep's cancel case (the id retired: `WireSt.retired`, no later response of it) and
// the registered Created case (`id ∉ seen`: never reused on the stream).
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
// Specs: wireStep (watchStep's compaction case: `cr ≤ σ.kv.compacted`, `done + 1 < cr`), kv's
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

// REQ v3rpcwatch/prev-kv: with PrevKv, an update's event that carries a previous record carries the
// key's previous one (a nil PrevKv says nothing: the registration's window,
// issues/etcd-watch-prevkv-before-created.md).
// Users: Kubernetes' etcd3 watcher (WithPrevKV: the previous object of an update or delete),
// client/v3/leasing (prevKV of deletes, through the client).
// Assumes: k is owned; nothing compacts.
// Specs: wireStep (EventM.isOf: WatchReq.prevOk, the history's record at the revision before, or
// none in the loose window).
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
		if ev.PrevKv != nil && string(ev.PrevKv.Value) != "1" {
			panic("prev-kv: the update's previous value")
		}
		return
	}
}

// REQ v3rpcwatch/fragments: the fragments of a response come contiguously, all of its id, neither
// a creation nor a cancel, the last without Fragment; reassembled, they are one response.
// Users: client/v3/watch.go:596-603 and :642 (run merges fragments into `cur` until one without
// Fragment).
// Assumes: the prefix pfx is owned and was never written before (a watch from the current revision
// may deliver events at or below its Created header's revision); nothing compacts; pfx+"\xff" is
// pfx's range end.
// Specs: wireStep (the pending fragment's conjunct, the fragment case), sendFragments.spec.
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
// Specs: wireStep's registered-Created case (`σa.permits who [(.read, w.range)] []` at a reached
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

// REQ v3rpcwatch/progress-notify: a watch created with ProgressNotify that gets a progress of its
// own id at revision P (no events) missed nothing up to P: its next event is above P.
// Users: grpc-proxy (proxy/grpcproxy/watch_broadcast.go:60, WithProgressNotify), Kubernetes'
// bookmarks (through 1b's client), raw tests (TestWatchWithProgressNotify).
// Assumes: k is owned; nothing compacts; the member's progress interval is finite (liveness only:
// the snippet just returns if the stream ends).
// Specs: wireStep (watchStep's progress case at the watch's id: no event in (done, P], done ≤ P).
func ReqProgressNotify(ctx context.Context, wc pb.WatchClient, kc pb.KVClient, k []byte) {
	p0, err := kc.Put(ctx, &pb.PutRequest{Key: k, Value: []byte("0")})
	if err != nil {
		return
	}
	ws, err := wc.Watch(ctx)
	if err != nil || ws.Send(createWith(&pb.WatchCreateRequest{Key: k,
		StartRevision: p0.Header.Revision + 1, ProgressNotify: true})) != nil {
		return
	}
	c, ok := recvCreated(ws)
	if !ok || c.Canceled {
		return
	}
	var P int64 = -1
	for P < 0 {
		r, err := ws.Recv()
		if err != nil {
			return
		}
		if r.WatchId == c.WatchId && len(r.Events) > 0 {
			panic("progress-notify: nothing was written to k after the watch's start")
		}
		if r.WatchId == c.WatchId && !r.Canceled && !r.Created && !r.Fragment {
			P = r.GetHeader().GetRevision()
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
				panic("progress-notify: the next event is above the progress revision")
			}
			return
		}
	}
}

// REQ v3rpcwatch/filters: a watch with the NOPUT filter delivers the range's deletes only.
// Users: raw tests (TestV3WatchWithFilter), grpc-proxy (FiltersFromRequest on its own requests),
// the Go client's WithFilterPut (through 1b).
// Assumes: k is owned; nothing compacts.
// Specs: wireStep (watchEvents filters by WatchReq.keeps), FiltersFromRequest.spec,
// filterNoPut.spec (through mvcc's filter contract).
func ReqFilters(ctx context.Context, wc pb.WatchClient, kc pb.KVClient, k []byte) {
	p1, err := kc.Put(ctx, &pb.PutRequest{Key: k, Value: []byte("1")})
	if err != nil {
		return
	}
	d, err := kc.DeleteRange(ctx, &pb.DeleteRangeRequest{Key: k})
	if err != nil {
		return
	}
	ws, err := wc.Watch(ctx)
	if err != nil || ws.Send(createWith(&pb.WatchCreateRequest{Key: k, StartRevision: p1.Header.Revision,
		Filters: []pb.WatchCreateRequest_FilterType{pb.WatchCreateRequest_NOPUT}})) != nil {
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
		if ev.Type != mvccpb.DELETE || ev.Kv.ModRevision != d.Header.Revision {
			panic("filters: the put is filtered out, the delete delivered first")
		}
		return
	}
}
