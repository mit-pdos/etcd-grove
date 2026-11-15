# Batch 1b (client watch), completeness review, round 1

Reviewer: completeness (README.md, "The review of a batch", 2). Read before `batch-1b.md`: the
specs (`ApiWatch.lean`, `watcher__{Watch,RequestProgress,Close}`, `Client__{Watch,RequestProgress}`,
`NewWatcher`, `NewWatchFromWatchClient`, `WatchResponse__{Err,IsProgressNotify}`, `OpWatch`), the
snippets (`examples/specreq/clientv3watch/*.go`, gofmt clean), the Go code (`.lake/src/client/watch.go`,
`server/.../v3rpc/watch.go`, `server/storage/mvcc/watchable_store.go`) and every user listed below.
The author's report was read only afterwards, to mark what it already says.

Paths: `C = .lake/src/client`, `S = .lake/src/server`, `K = /home/ubuntu/go/pkg/mod/k8s.io/apiserver@v0.0.0-20261021221356-9c4ec15b8038/pkg/storage`,
`X = examples`.

## Users and patterns

| pattern | call sites | snippet | pre / post at one site |
|---|---|---|---|
| start at a Get's revision + 1, apply events as deltas | `C/mirror/syncer.go:119`, `C/naming/endpoints/endpoints_impl.go:131`, `S/.../v3discovery/discovery.go:370`, `C/leasing/kv.go:174,210`, `.lake/src/cache/cache.go:392` (after `get`, `cache.go:335`), `K/etcd3/watcher.go:481-493` | `from-get` | cache: `Watcher.WatchTriple` with `internalCtx` (`ctxOk`, `ctxPrin`), opts `WithPrefix, WithRev, WithProgressNotify, WithCreatedNotify` (no `watchPanics`); post sufficient for `validateRevisions` (`store.go:178`): events strictly above the position, progress `≥` position (`watchStep`'s `c ≤ P`). OK |
| start at a Get's revision (inclusive) | `C/concurrency/key.go:30` via `waitDeletes` (`key.go:61`: `resp.Header.Revision`), `C/concurrency/election.go:190` | `wait-delete` (from `+1`; the header calls `key.go:30` "revision + 1", which it is not: minor, S6) | only liveness and "a DELETE event" are relied on. OK |
| explicit old revision, full-history check | `X/etcd/watch/watchkv.go:79`, `X/etcd/partition/linkv3p.go:193`, `X/etcd/auth/authkv.go:434,445`, `X/etcd/compactwatch/compactkv.go:122` (`etcdstart.Collect`/`Check`, `X/lib/etcdstart/watch.go:94,144`) | `history`, `order` | `WatchPos.init 1 = some 0`, then `watchEvents` from 1: `Check`'s gap-free-from-2 follows under the owner's invariant. OK |
| future revision (never reached) | `S/proxy/grpcproxy/leader.go:62` (`MaxInt64-2`) | none needed (liveness) | OK |
| **current revision (`rev = 0`)** | `S/proxy/grpcproxy/watch_broadcast.go:68` (coalescing, `bcast` `:78-81`, `add` `:89`, `watcher.send` `:62-64`), `S/proxy/grpcproxy/health.go:73`, `X/k8s/compactor/compactor_test.go:104-108`; `ReqWatchEnds/Filter/Rewrite` use it for per-response facts only | none for completeness | **F3** |
| `WithPrefix` / `WithRange` / `WithFromKey` / `""` | prefix everywhere; `WithRange`: `authkv.go:445`, `C/namespace/watch.go:45`, grpcproxy `watch_broadcast.go:59`; whole keyspace `authkv.go:434` | prefix only | `OpM.watchReq` + `KeyRange.mem` cover all three; no snippet exercises `WithRange`/`""` (S3) |
| `WithPrevKV` | `K/etcd3/watcher.go:481` (`event.go:67`: nil `PrevKv` on a non-create is an error, handled), grpcproxy | `prev-kv` (no compaction) | `prevOk` gives "if non-nil, the previous value" under compaction too; k8s handles nil. OK |
| filters | none outside grpcproxy (forwards) | `filter` | OK |
| `WithProgressNotify` + progress as a bookmark | `K/etcd3/watcher.go:486,508`, cache `demux.go:201`, grpcproxy | `progress-complete`, `order` | OK (position known: every such user passes a revision, except grpcproxy, F3) |
| `RequestProgress` | `.lake/src/cache/progress_requestor.go:94`, `K/etcd3/store.go:108`, `K/etcd3/watcher.go:303`, `X/etcd/cache/cachekv.go:162` | `request-progress` | ctx is `WithRequireLeader(ctx)` (k8s): `WithRequireLeader.spec` gives `ctxOk` and keeps `ctxPrin`. Post `True`: errors are logged. OK |
| `WithCreatedNotify`, `Created` first | cache (readiness, `cache.go:401`), grpcproxy leader/health/broadcast, `X/etcd/watch/watchkv.go:79` | `created-first` | OK |
| `WithRequireLeader` contexts | every k8s watch (`K/etcd3/store.go:1162`) | none (S3) | establishable (above) |
| `WithWatchBufLog` | `K/etcd3/watcher.go:489-491` | none (S3) | `opWatchM` carries it; the code path it enables (`newWatcherStreamBufLogger`, `startBufWait`/`recordBufWait`) is not exercised by a snippet |
| range over the channel / `select` with ctx | range: recipes, k8s, leasing, discovery, `waitDelete`, namespace; select: cache `cache.go:399`, endpoints `:133`, Election `:198` (bare receive) | `select` (+ all the range ones) | OK |
| check `Err()`; check `Canceled` / `CompactRevision` without `Err()` | `Err()`: nearly all; `Canceled || CompactRevision`: `X/etcd/cache/cachekv.go:187`; `CompactRevision` alone: `X/lib/etcdstart/watch.go:124` (`CompactRev`) | `compacted`, `ends` | **F1** for `CompactRevision` alone |
| no `Err()` check: relies on an error response having no events | `C/concurrency/election.go:223-246`, `S/.../v3discovery/discovery.go:376`, `C/leasing/kv.go:175` | `ends` | OK |
| rewrite the response (header revision, keys) | `C/concurrency/election.go:205` (`hdr.Revision = kv.ModRevision`), `C/namespace/watch.go:59-62` | `rewrite` | OK (`hdrDq`, `eventOwn` at `own 1`) |
| **share a response's events / header among many readers** | cache: `demux.go:281` hands the same `[]*mvccpb.Event` to every watcher and to the history ring (`demux.go:218,227`); Election `election.go:238-241` hands one `wr.Header` to several `GetResponse`s | none | **F2** |
| restart after an error / close from the last position + 1 | k8s reflector via `K/etcd3/store.go:1151` (`WithRev(rv+1)`, `rv` an event's or a bookmark's), cache (`cache.go:335` relists; `demux.Init` `demux.go:137` keeps history if `rev == maxRev+1`) | none (S2) | provable from `etcdLb_ord` (`State.lean:103`) and `watchStep`; no snippet checks it |
| compaction retry / `CompactRevision` value | cache relists, k8s "too old", `X/etcd/compactwatch/compactkv.go:142` (C3) | `compacted` | **F1**, and C3 below |
| refused watch (auth) | `X/etcd/auth/authkv.go:272` (with a caller-built `token` metadata, `:269-271`) | `refused` | `ctxPrin` for a context with the caller's own `token` needs 2a's introduction (already in `req/google_golang_org_grpc.md` item 7). OK as tracked |
| stop: ctx cancel, `Close` | every user cancels; `Client.Close` (`C/client.go:150`), `C/namespace/watch.go:79` | `close` | OK |
| a `nil` channel check | `C/experimental/recipes/watch.go:29,39` | none | handled without panic; 1f asked for "non-nil" (S1) |
| the client's `Watcher` field replaced by a wrapper | `S/.../v3client/v3client.go:40,66` (`watchWrapper`, `blankContext`), `S/etcdmain/grpc_proxy.go:483` (`namespace.NewWatcher`) | none | S4 |

## First tier

### F1. An error response with `closeErr` may carry any `CompactRevision`: `ReqWatchCompacted` and compactwatch's C3 are unprovable

`watchStep`'s error case (`ApiWatch.lean:235-238`) constrains `compactRev` only under
`m.closeErr = none`. With `closeErr = some k` and `compactRev ≠ 0` every conjunct holds, so the spec
admits a response the code never sends: every `closeErr` response is built as
`WatchResponse{Header: &pb.ResponseHeader{}, Canceled: true, closeErr: ...}` (`C/watch.go:366,381,500`),
`CompactRevision = 0`, header revision `0`.

- `ReqWatchCompacted` (`ending.go:19-34`): on `wr.CompactRevision != 0` it panics unless
  `wr.Err() == rpctypes.ErrCompacted`; with `closeErr = some k`, `WatchResponse.Err.spec` gives
  `callErr err k` for an unconstrained `k`, so the panic is not excluded.
- `etcdstart.CompactRev` (`X/lib/etcdstart/watch.go:119-128`) reads `CompactRevision` without
  `Err()`: compactwatch's `checkCompactRev` (`compactkv.go:139-152`) and the k8s compactor test
  (`X/k8s/compactor/compactor_test.go:51,186`) get no fact about `crev` from such a response.

Fix: in the error case, `m.closeErr ≠ none → m.compactRev = W64 0` (and `m.hdr.revision = W64 0` if
wanted), or state the compaction clause as `m.compactRev ≠ W64 0 → m.closeErr = none ∧ ∃ cr, …`.

### F2. No law makes a received response's events or header shareable: the cache and `Election.observe` are not served

`watchRespAt_fields` gives `msgsOwn eventOwn v.Events' (own 1)` and `respHeaderOwn v.Header' m.hdrDq`;
nothing turns them read-only. W0's `replyPersist` (`api/v3/Wire.lean:262`) covers the five KV
replies only, and `protoRest` (inside `eventOwn_unfold`, `keyValueOwn_unfold`,
`respHeaderOwn_unfold`) has no law of its own, so the client cannot persist them by unfolding.

- The cache hands one response's `*mvccpb.Event`s to every active watcher (`cache/demux.go:281`) and
  keeps them in its history ring (`demux.go:218,227`): an unbounded number of readers.
- `Election.observe` forwards one `wr.Header` in several `GetResponse`s (`election.go:238-241`).

1g asked for exactly this (`req/go_etcd_io_etcd_client_v3.md`, "from 1g", item 2:
`eventOwn p (own 1) e ⊢ |==> eventOwn p discard e`, and `watchRespAt v m ⊢ |==>` its read-only
form); `ApiWatch.lean` and `batch-1b.md` do not answer it. Fix: a law
`watchRespAt_persist.spec : watchRespAt v m ⊢ |==> (read-only form)` with `eventOwn_persist.spec`
(and `respHeaderOwn`'s, W0's, or make `eventOwn`/`respHeaderOwn` part of `replyPersist`'s family);
a snippet: two goroutines reading the same response's events.

### F3. A watch from the current revision gets no completeness at all, though its users rely on one the code gives

`WatchPos.init 0 = {done := none}` and the `Created` case leaves `done` unknown, so a `rev = 0`
watch says nothing about which events it will deliver until its first event. The author's report
(finding 1, decision 2) says "No user found relies on `rev = 0` completeness (every user passes
`WithRev`)". Two do, and the `Watcher` documentation promises it (`C/watch.go:68-69`: "If the
requested revision is 0 or unspecified, the returned channel will return watch events that happen
after the server receives the watch request"):

- grpcproxy's coalescing: a broadcast watch from `wb.nextrev = 0` (`watch_broadcast.go:57-68`)
  sets `nextrev := H + 1` from its first response, the `Created` at header `H` (`:78-81`), then admits
  receivers with an explicit start `≥ H + 1` (`add`, `:89-96`), which rely on every event above `H`
  coming through it; a proxied current watch does the same per receiver (`watcher.go:62-64`).
- `X/k8s/compactor/compactor_test.go:104-108`: a `rev = 0` watch, then a workload whose every put
  must appear ("registered (Watch returns before it is) before the workload starts").

What the code gives is weaker than the author's rejected alternative ("complete from the member's
registration revision", which needs a server change) and is true today: `Watch` returns the channel
only once `serveSubstream` has the `Created` response (`watch.go:849-871`), which sets
`nextRev := H`; before any event a resume re-registers from `H`, after an event from the last
event's `+ 1`. So **every event of the range above `H` is delivered, in order**, while some events
at or below `H` may or may not be (the author's (a), (b)); and `H` is at most the cluster's revision
when `Watch` returns. Suggested restatement: a field `floor : Option Nat` of `WatchPos`, set by
`Watch`'s post for `rev = 0` to the revision of a state reached at its return
(`∃ σ, etcdLb γ σ ∗ watchChAt … {floor := some σ.kv.rev, done := none, …}`), with the event case
at `done = none` requiring `lo ≤ f + 1` when `floor = some f` (events at or below `f` may come,
none above `f` is skipped); a progress at `P` keeps saying nothing while `done = none` (a progress
below `H` is the author's (c)). The provability reviewer should check the restatement against `serveSubstream` and
`issues/etcd-watch-progress-before-created.md`. If the author keeps the current statement, it is an
open question for the user with these two users named (grpcproxy is no batch's; the test is a test),
not "no user".

## Second tier

- **S1. Two requests of other batches unanswered.** (a) 1d, item 3 (`req/…client_v3.md`, "from
  1d"): non-decreasing header revisions along a channel. False of the code, so the spec is right not
  to give it, but say so to 1d with the case: an unsynced watcher's batch is cut at
  `watchBatchMaxRevs` with the header at the store's revision (`S/storage/mvcc/watchable_store.go:397-401`),
  so a response can have header `H` and last event `c' < H`; after a reconnect to a member at a
  revision in `(c', H)`, the next event response's header is below `H`. 1d must drop the order from
  `observeAt_recv`. (b) 1f, item 1: `Watch` returns a non-`nil` channel. True (`watch.go:488-491`
  "never hand Watch a nil channel"; the closed channel of `:362-384` is `make`'s); add `⌜ch ≠ null⌝`
  to `WatchTriple`'s post (or a law `watchChAt_ne_null`). The recipes handle `nil` without a panic
  (`recipes/watch.go:29`), but their specs return `ErrNoWatcher` otherwise.
- **S2. Missing snippet: chaining watches.** Kubernetes' reflector re-watches from the last
  resource version, which may be a bookmark's (`K/etcd3/store.go:1151` → `watcher.go:481`
  `WithRev(rv+1)`), and the cache's demux continues its history across watches when the new start is
  `maxRev + 1` (`demux.go:137`). A snippet: watch A to an event or progress at `c`, end it, watch B
  from `c + 1`; the concatenation equals the history (panic on a gap or a repeat). It checks that
  `watchStep`'s facts compose across watches (`etcdLb_ord`), which no current snippet does.
- **S3. Options and contexts no snippet exercises.** `WithWatchBufLog` (k8s, `watcher.go:489-491`:
  enables `newWatcherStreamBufLogger`, the buffer-wait timing, a logger), a `WithRequireLeader`
  context (every k8s watch), `WithRange` and the empty key with `WithPrefix` (`authkv.go:434,445`,
  namespace). The spec covers them generally; one "calls do not panic" snippet with these would
  check the preconditions are met for them.
- **S4. Users whose `Watcher` is not a `*watcher` or whose context names another principal.**
  `v3client.New` installs a `watchWrapper` that wraps the context in `&blankContext{ctx}`
  (`S/.../v3client/v3client.go:40,62-67`; used by `embed/serve.go:148`, hence v3election/v3lock):
  `isClient` for that client needs `watcherAt` of the wrapper, i.e. `ctxOk`/`ctxPrin` of a
  `blankContext` (promoted methods; a law of 1c/W0's). grpcproxy forwards a downstream client's
  token (`watch_broadcast.go:66` `withClientAuthToken`), which `ctxPrin ctx who` excludes for the
  proxy's own `who`; the namespace wrapper as the client's `Watcher` (`etcdmain/grpc_proxy.go:483`)
  cannot meet `watcherAt` for the same `γ` (keys are stripped). All outside every batch; record them
  in `batch-1b.md` as known unserved users rather than leave them unlisted.
- **S5. compactwatch's C3 can be stated once F1 is fixed and W0 adds the retention** (the author's
  open question 2, confirmed). `EnvStep.compact` (`api/v3/Model.lean:1144`) allows `r ≤ σ.kv.rev`;
  etcd's revision-mode compactor compacts at `rg.Rev() - retention` (`S/.../v3compactor/revision.go:81`),
  a member's revision, so `r + retention ≤ σ.kv.rev`; periodic mode (cachekv's
  `StartPeriodicServer`) gives no revision gap, so `EnvCfg` needs the mode, not a bare `Bool`. The proof
  then: `CompactRev`'s response is the compaction case (F1) with `etcdLb γ σ` and `cr ≤ σ.kv.compacted`;
  the owner's invariant "`compacted = 0 ∨ compacted + 1 ≤ rev`" is stable under the example's own
  `Compact(presp.rev - 1)` and the revision-mode step; at the later `Get`, `etcdLb_reach` and the
  model's monotonicity of `compacted` along `Reach` (a pure lemma the client proves) give
  `crev + 1 ≤ lresp.Header.Revision`. Nothing more is needed of 1b.
- **S6. Snippet headers.** `ReqWatchWaitDelete` cites `key.go:30` as a watch "from a key's revision
  + 1"; `waitDeletes` passes the Get's revision itself (`key.go:61`), as `election.go:189` does. The
  `prev-kv` snippet assumes no compaction; Kubernetes' pattern is "under compaction, a non-nil
  `PrevKv` is the previous record, a nil one is an error" (`K/etcd3/event.go:67`), which `prevOk`
  gives; a variant without the no-compaction assumption would cover it. `watcher__Watch.lean`'s
  Users omit `watch_broadcast.go:68` and `health.go:73` (and F3's reliance).
- **S7. The author's grpcproxy finding 2 is probably not a bug** (uncertain): a receiver added at
  `w.nextrev = H + 1` after an event response with header `H > c'` does not miss events at or above
  its start: the later responses carry the events of `(c', H]` (dropped by `watcher.send`,
  `watcher.go:59,72`, as below its start) and then the events above `H`. The proxy's real exposure
  is `rev = 0` with progress (the author's 1(c)), which F3's floor would keep out.

## What is good

- One persistent fact per response (`etcdLb` + pure `watchStep`) in place of the old per-response
  update: every pattern above that concludes something (exact history, bookmarks, compaction
  floors) is a pure consequence, and chaining across watches works through `etcdLb_ord`.
- The relaxations match the users: any range including the empty key normalized, any start
  revision, any `ctxOk` context with `ctxPrin` (k8s' `WithRequireLeader` included), filters,
  `prevKV` with the compaction disjunct, fragments, auth with the admitting state `σa`.
- Ownership of a response matches what users do (header written by `Election.observe`, keys by the
  namespace wrapper, a broadcast progress's header read-only).
- Errors end the watch with only error responses after: exactly what `Election.observe`,
  discovery and leasing rely on without checking `Err()`.
- `Watcher` as an interface bundle filling W0's `watcherAt`: the cache, which holds a `Watcher`
  interface value, is served without dispatch glue.

## Ranking (need of revision)

1. `ApiWatch.lean`: F1 (`watchStep`), F2 (a persist law), F3 (`WatchPos`/`WatchTriple`), S1(b).
2. `examples/specreq/clientv3watch/`: snippets for F2, S2, S3; headers (S6).
3. `watcher__Watch.lean` (Users, F3's margin), `batch-1b.md` (answers to 1d/1f/1g, S4's unserved users).
4. `WatchResponse__Err`, `WatchResponse__IsProgressNotify`, `watcher__RequestProgress`,
   `Client__RequestProgress`, `watcher__Close`, `NewWatcher`, `NewWatchFromWatchClient`,
   `Client__Watch`: no change needed for completeness.

## Verdict

Not done: three first-tier findings. F1 is a one-conjunct fix; F2 a law (already requested by 1g);
F3 either a restatement (a floor for `rev = 0` watches) or an open question for the user with the
two relying users named.
