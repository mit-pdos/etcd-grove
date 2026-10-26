---
upstream: none
checked: 2026-10-26
links:
  - etcd-io/etcd#15237 pr merged: progress responses go through mvcc's watch channel (ordered after the stream's queued events), but a watch's Created response still goes on ctrlStream and can overtake a queued broadcast progress response; the path of the 2026-10-23 end-to-end reproduction (issues/etcd-watch-progress-before-created.md)
  - etcd-io/etcd#20221 issue closed: same trigger on the server side (a member switched to by a multi-endpoint client sent progress notifications below the watch's start revision); not the cache's missing check
  - etcd-io/etcd#20229 pr merged: the server fix of that trigger (progressIfSync sends no progress while rev < w.startRev; backported to 3.5 and 3.6, #20245, #20241), which keeps a fixed etcd from sending the stale progress this finding needs; the demux still accepts one
  - etcd-io/etcd#20614 pr merged: related (made the demux progress-aware: Broadcast's progress handling, maxRev); no discussion of a progress below minRev
---

# A progress notification below the cache's start revision makes a watch "from now" compacted

- **Status**: bug (a wrong result: a spurious `ErrCompacted`), reproduced end to end against one
  etcd member at upstream `main` `3aaab3479` (2026-10-23, below), as well as at the demux level. The
  2026-10-20 reading below ("not reachable with one member", "nor with #20229") was wrong: #20229
  closes the lagging-member trigger, but a broadcast progress response that the server computed
  before the cache's watch existed can still reach it after its `Created`
  (`etcd-watch-progress-before-created`). Superseded reading, kept for the record: both
  per-watcher progress paths (`RequestProgress`, `v3rpc/watch.go:564`, and the periodic one) and
  `RequestProgressAll` (398) go through `progressIfSync`, which sends nothing while
  `rev < w.startRev` (`server/storage/mvcc/watchable_store.go:528`), so a lagging member sends no
  progress to the cache's watch from `R + 1` until it reaches it.
- **2026-10-23, checked against upstream `main` `3aaab3479`** (the user's assessment was "a non-issue:
  the latest client guarantees no stale progress notifications"). Verdict: **real**. Neither side
  guarantees that:
  - client (`client/v3/watch.go`): a progress response with watch id `-1` (the answer to
    `RequestProgress`) goes to every substream in `substreams` when it is received
    (`broadcastResponse`, 738), including one moved there by a `Created` (475) the server sent after
    computing the progress; `serveSubstream` (789) forwards a progress response below the watch's
    start revision without a check, and even lowers its resume revision to it
    (`nextRev = wr.Header.Revision + 1`, 864). The client's progress fixes (`36fc3cae6`, the nextRev
    on a progress response; #17557, `6103504d4`) are about resumes and watches with no events, not
    this.
  - server: `progressIfSync` (`watchable_store.go` 517–543) covers only the watchers in the stream's
    map when it runs, at `s.rev()` (#20229 adds `rev < w.startRev`, 528, which does not help a
    watcher that does not exist yet). #15237 (`74feb229c`) puts the progress response on mvcc's
    channel, but `sendLoop` selects between that channel (`v3rpc/watch.go` 435) and `ctrlStream`
    (514), and a later create's `Created` goes on `ctrlStream` (367), so it can overtake the queued
    progress response (not fixed at `main`: the fork's fix `09669450f` is not upstream).
  - cache: it watches through `client.Watcher` (`cache.go` 84) with `internalCtx`, a context
    without metadata, so its watch shares the client's gRPC watch stream with every other watch and
    `RequestProgress` on that client made with a context without metadata (the common case). The
    first response (`Created`) runs `demux.Init(R + 1)` (406); the stale progress then passes
    `validateRevisions(resp, d.maxRev)` with `maxRev = 0` (`demux.go` 151) and becomes `maxRev`
    (201). The cache's own store is not affected (its watcher, at `R + 1`, is skipped by
    `broadcastProgressLocked`, 239), only the watches registered afterwards (`Register`, 99).

  End-to-end reproduction (`tests/integration/zz_cache_stale_progress_test.go`,
  `TestCacheStaleProgressCompactsNewestWatch`, in the scratch worktree
  `~/etcd-fixes/stale-progress-investigate`, detached at `3aaab3479`, uncommitted; run from
  `tests/` with `go test ./integration -run TestCacheStaleProgressCompactsNewestWatch -count=1 -v`):
  one member; eight watches on `/busy/` with `WithPrevKV` on the client's shared stream and a writer
  of 100-put txns with 12 KiB values keep the server's `sendLoop` busy; per trial, another goroutine
  of the same client calls `cli.RequestProgress` every 200 µs until the cache's `Get` starts (a
  `KV` wrapper stops it there, so every progress request precedes the cache's watch on the stream),
  then `cache.New(prefix)`, `WaitReady`, a 10 ms pause, `c.Watch(ctx, prefix+"x")` with no revision
  and a `Put` of `prefix+"x"`. A `Watcher` wrapper records progress responses below the cache's
  `Get` revision. Failing trace: `the cache's watch (from 1648, after its Get at 1647) received a
  progress notification at 1646`, then `a cache watch from now was canceled (compact revision 1647,
  "etcdserver: mvcc: required revision has been compacted")` — `maxRev = 1646`, the watch starts
  at `1647 < minRev = 1648` and is compacted when the `Put`'s event arrives. It failed in 6 of 8
  runs of up to 500 trials (first hit after 19 to 499 trials); in the passing runs the cache's
  watch received a stale progress in about a third of the trials, but a fresher progress raised
  `maxRev` before the client watch registered. (The writer's periodic etcd `Compact` at
  `rev - 10` only keeps the backend under its quota; the reported compact revision is the demux's,
  `r + 1`.) A raw-watch variant in the same file (`TestRawStaleProgressAfterCreated`: `RequestProgress`,
  `Get` at `R`, `Watch(WithRev(R + 1), WithCreatedNotify())`) sees a progress at `R - 1` after
  `Created` in about 1% of trials.

  So the trigger is a concurrent `RequestProgress` on the same client (or the cache's own
  progress requestor, which runs while cache `Get`s wait, when the cache re-creates its watch).
  It does not need several members, and #20229 does not prevent it. The proof does not reach it
  because the verified fork has the `Created`-ordering fix (`09669450f`), under which a broadcast
  progress response is sent before any later `Created`. Fixing either side would close it: the
  demux check (Possible fixes, below) or the server ordering fix
  (`issues/upstream/etcd-watch-progress-before-created/`).
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
- **How the proof handles it**: the proof's etcd is one server running the verified fork, which has
  the `Created`-ordering fix (`09669450f`); there a progress revision is never below a revision a
  previous response reported. Upstream `main` lacks that fix, so this holds only for the fork. The cache's watch contract (`watchRespOk`,
  `Proof/go_etcd_io/etcd/cache/v3/InvEtcd.lean`) requires a progress notification to be at or above
  the watch's position; the W-K unit proves that from the server (`notes/status-history.md`, "W-K", K2e).
- **Possible fixes**: validate a progress notification against `max(maxRev, minRev - 1)` in
  `Broadcast` (the revision the demux was initialized from); or have `Init` set `maxRev` to
  `minRev - 1`.
- **Found**: 2026-10-17, unit W-K (the start revision of the cache's watch against the first
  progress notification).
