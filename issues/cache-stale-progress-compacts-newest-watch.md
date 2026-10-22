---
upstream: none
checked: 2026-10-21
links:
  - etcd-io/etcd#20221 issue closed: same trigger on the server side (a member switched to by a multi-endpoint client sent progress notifications below the watch's start revision); not the cache's missing check
  - etcd-io/etcd#20229 pr merged: the server fix of that trigger (progressIfSync sends no progress while rev < w.startRev; backported to 3.5 and 3.6, #20245, #20241), which keeps a fixed etcd from sending the stale progress this finding needs; the demux still accepts one
  - etcd-io/etcd#20614 pr merged: related (made the demux progress-aware: Broadcast's progress handling, maxRev); no discussion of a progress below minRev
---

# A progress notification below the cache's start revision makes a watch "from now" compacted

- **Status**: bug (a wrong result: a spurious `ErrCompacted`), reproduced at the demux level; an
  end-to-end reproduction needs an etcd member that lags behind the one the cache's `Get` read
  (not attempted). Not reachable with one etcd member: the proof's model. Nor, it appears, with
  a server that has etcd-io/etcd#20229 (v3.5 and v3.6 backports, and the pin): both progress
  paths (`RequestProgress`, `v3rpc/watch.go:564`, and the periodic `RequestProgressAll`, 398) go
  through `progressIfSync`, which sends nothing while `rev < w.startRev`
  (`server/storage/mvcc/watchable_store.go:528`), so the lagging member sends no progress to the
  cache's watch from `R + 1` until it reaches it; what remains is the demux's missing check
  (checked by code reading, 2026-10-20).
- **Where** (`upamanyus/etcd` `goose-lean` `09669450f`, `cache/`):
  - `cache.go`: `get` (340) reads the prefix and restores the store at the `Get`'s header
    revision `R`; `watch(R + 1)` (348) calls `demux.Init(R + 1)`, which on a fresh demux sets
    `minRev = R + 1` and leaves `maxRev = 0` (`demux.go` 120–130);
  - `cache.go` `watchEvents` (391) watches from `R + 1` (`WithProgressNotify`, `WithCreatedNotify`)
    and sets the cache ready on the first response (408), the `Created` one, which leaves `maxRev`
    at `0`; `waitTillRevision` (268) then has the progress requestor send `RequestProgress` RPCs
    (273) when a client asks for a revision the cache has not reached;
  - `demux.go` `Broadcast` (146) checks a progress notification only against `maxRev` (152,
    `validateRevisions`: `progress < latest` is an error), which is `0` on a fresh demux, so any
    progress revision passes and becomes `maxRev` (202);
  - `Register` (85) with no revision then makes a watcher active at `maxRev + 1`; the first
    batch of events, at `R + 1`, is above that, so `broadcastEventsLocked` moves it to the lagging
    watchers (263), and `resyncLaggingWatchers` compacts it, `nextRev < minRev` (330).
- **What happens**: the cache reads at `R` from an up-to-date member; its watch is served by a
  member at `P < R` (the client balances RPCs across endpoints; a watch is served from the
  member's local store); that member answers a progress request with `P` before it catches up.
  The demux takes `maxRev = P`. A client watch with no revision, registered then, is cancelled with
  `ErrCompacted` at `P + 1` when the events from `R + 1` arrive, instead of receiving them.
  Demux-level reproduction (in package `cache`):

  ```go
  func TestDemuxStaleProgressCompactsNewestWatch(t *testing.T) {
  	d := newDemux(16, time.Hour)
  	d.Init(11)
  	if err := d.Broadcast(clientv3.WatchResponse{Header: &etcdserverpb.ResponseHeader{Revision: 5}}); err != nil {
  		t.Fatalf("stale progress rejected: %v", err)
  	}
  	w := newWatcher(16, nil)
  	d.Register(w, 0)
  	ev := &mvccpb.Event{Type: mvccpb.PUT, Kv: &mvccpb.KeyValue{Key: []byte("k"), ModRevision: 11}}
  	if err := d.Broadcast(clientv3.WatchResponse{Header: &etcdserverpb.ResponseHeader{Revision: 11}, Events: []*mvccpb.Event{ev}}); err != nil {
  		t.Fatal(err)
  	}
  	d.resyncLaggingWatchers()
  	select {
  	case _, ok := <-w.respCh:
  		if !ok && w.cancelResp != nil && w.cancelResp.CompactRevision != 0 {
  			t.Fatalf("a watch from now was compacted at %d", w.cancelResp.CompactRevision)
  		}
  	default:
  	}
  }
  ```

  It fails (`a watch from now was compacted at 6`); without the progress at `5` the same watch
  receives the event (checked 2026-10-17, `go test ./ -run TestDemux` in `cache/`).
- **Expected**: a watch with no revision starts at the cache's latest revision and is not
  compacted; a progress notification below what the cache has already reached carries no news
  and should be rejected or ignored, as `Broadcast` does once `maxRev` is set.
- **How the proof handles it**: the proof's etcd is one server, where a progress revision is never
  below a revision a previous response reported. The cache's watch contract (`watchRespOk`,
  `Proof/go_etcd_io/etcd/cache/v3/InvEtcd.lean`) requires a progress notification to be at or above
  the watch's position; the W-K unit proves that from the server (`notes/STATUS.md`, "W-K", K2e).
- **Possible fixes**: validate a progress notification against `max(maxRev, minRev - 1)` in
  `Broadcast` (the revision the demux was initialized from); or have `Init` set `maxRev` to
  `minRev - 1`.
- **Found**: 2026-10-17, unit W-K (the start revision of the cache's watch against the first
  progress notification).
