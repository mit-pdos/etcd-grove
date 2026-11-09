# Batch 2b (gRPC watch service), provability review, round 1

Reviewer: provability. Sources: `.lake/src/server/etcdserver/api/v3rpc/watch.go` (the fork at
`a4d2bb17`), `.lake/src/server/storage/mvcc/{watcher,watchable_store,watcher_group}.go`,
`.lake/src/client/watch.go`, the translation `Code/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc.lean`,
1b's `Spec/go_etcd_io/etcd/client/v3/ApiWatch.lean` **as in the working tree** (its `wireStep` has
adopted the `-1` correction, uncommitted at `ee73fab54d`). I wrote my findings before reading
`notes/specs-only/batch-2b.md`. The author did not find any of the first-tier ones below.

## First tier

### F1. `sendLoop` (hence `srvWireStep`'s `prevOk`) is false with `PrevKv`: a race in the Go code drops `PrevKv` from a new watch's first events

`watch.go:443-445` reads `needPrevKV := sws.prevKV[wresp.WatchID]` **before** the `ids` check at
`:468-475` that buffers a not-yet-announced id's responses. `recvLoop` sets `sws.prevKV[id] = true`
only after `watchStream.Watch` has returned (`:342` then `:344-349`, under `mu`). Between the two,
mvcc can already have queued a response of the new watcher: `notify` sends synchronously from a
concurrent write's `End` (`watchable_store.go:481-505`) for a synced watcher, and `syncWatchers`
for an unsynced one (a watch from a past revision, Kubernetes' pattern). The send loop then reads
`prevKV[id] = false`, builds the events without `PrevKv`, buffers them in `pending`, and flushes them
unchanged after the `Created` (`:571-581`). The client receives an update or delete event of a
`WithPrevKV` watch with `PrevKv == nil`, above the compaction.

* Violates 1b's `WatchReq.prevOk` (`pk = none` only for a creation or below the compaction), which
  `sendLoop.spec`'s sketch claims for every sent event, and `WatchInternal.lean`'s invariant "`prevKV[id]`
  ... the registration's `w.prevKV`" (false between `Watch` and the lock).
* User impact: Kubernetes' etcd3 watcher fails the watch on it
  (`k8s.io/apiserver@v0.37.2/pkg/storage/etcd3/event.go:65`: "etcd event received with
  PrevKv=nil"). Snippet `ReqPrevKV` is "provable" from the spec only because the spec is unsound.
* Upstream has the same order (the code predates the fork); found by code reading, no test. Not
  in `issues/`/`nonissues/` (I searched for `needPrevKV`, `prevKV[`). **To file** (I am read-only):
  `issues/etcd-watch-prevkv-before-created.md` if a test reaches it (an integration test creating
  many `WithPrevKV` watches from a past revision under concurrent puts, or a sleep/failpoint
  between `Watch` and the lock), else `nonissues/`; `blocks-proof: yes` for 2b.
* Fix (the fork, like `issues/etcd-watch-progress-before-created.md`'s drain): look up `prevKV`
  after the `ids` check, i.e. buffer the raw `mvcc.WatchResponse` in `pending` and build `wr`
  (with its `Range`s) when it is flushed; or hold `sws.mu` across `watchStream.Watch` in
  `recvLoop` (no deadlock: mvcc never blocks on `ws.ch`, `w.send` uses `select … default`). Then
  the sketch's invariant holds as stated. Until then the spec must either put `prevKV` out of scope
  again or weaken `prevOk` for the first responses of a watch (bad for Kubernetes): a decision.

### F2. The `-1` correction is real and sound for the member, but with it 1b's `wireStep` no longer lets the Go client prove its broadcast: `Created` ids must be fresh over the whole stream

(Check (b).) The race the correction answers is real: `Cancel(W)` removes `W` from
`ws.watchers` (`watcher.go:153-176`), `RequestProgressAll` then sends a `-1` progress if the
*remaining* watchers are synced (`watchable_store.go:528-553`; it needs at least one other
watcher, else it sends nothing), and the send loop's `select` (`watch.go:514-603`) may take that
progress before the cancel response on `ctrlStream`. The exemption (`cancel r.1 ∈ ss`) is minimal
and the member's proof can supply it (the run's canceled set with its received requests).

But the client side: 1b's `run`/`deliverOk` sketch (`WatchInternal.lean` of 1b, lines 51-53) argues
"a substream in `r.subs` never had its cancel sent: `run` cancels only ids with no substream ...".
That needs, at each `addSubstream` (`client/watch.go:605-613`), that the new `Created` id was never
the object of an earlier cancel the client sent. The client sends cancels for ids it received:
on `closingc` (`:696-715`) and **for any response of an id with no substream**
(`:655-673`, "failed dispatch"). `wireStep` allows both (a response of an unregistered id is
"nothing"; a `Created` needs only `st.reg m.watchId = none`, so an id whose registration ended can
be `Created` again). So under `wireStep` a client can have sent `cancel X`, then receive `Created X`,
add a substream `X`, and then get no progress fact for it from a `-1` response, which it broadcasts
to `X`: 1b's proof is stuck. The real member never does this (mvcc's auto ids only grow,
`watcher.go:129-135`; a response is sent only for an id in `ids`, i.e. after its `Created`,
`watch.go:468-475`; after an id's cancel response it leaves `ids` and is never re-announced).

Restatement (for 1b's `wireStep`, which 2b's `srvWireStep` now equals, F6): give `WireSt` the ids
announced so far, `seen : List Int`; a registered `Created` requires `m.watchId ∉ st.seen` (and
adds it); a response of an id with no registration requires `m.watchId ∈ st.seen` (no response of a
never-created id); and, for F3's `ReqCancel`, `retired : List Int` (ids whose cancel response was
sent; a compaction response does not retire, since `issues/etcd-watch-compacted-resent.md` lets mvcc
resend it) with no response of a retired id. The member proves all three from the facts above; the
client derives "every id it ever cancelled is in `seen` before any `Created` of it", hence the
exemption never meets a substream.

### F3. Snippets unprovable from `srvWireStep` (= `wireStep`)

* **`ReqCreatesInOrder`**: panics if the first create (`s = 0`) is refused and if the second
  (`s = -1`) is not. `wireStep`'s `Created` case states nothing about *when* a create is refused
  (the `canceled` branch has no condition), and its registered branch admits `s < 0`
  (`WatchPos.init (-1) H`). The member gives both: refused iff `s < 0`, or `isWatchPermitted` failed,
  or mvcc refused (an empty range, `watcher.go:117-119`). Either add to the registered branch
  `0 ≤ s` and to the refused one `s < 0 ∨ w.range empty ∨ ∃ reached σ', ¬ σ'.permits who …`
  (auth refusals also come from a stale token, `ErrAuthOldRevision`, so the honest disjunct is
  weaker than "not permitted": "some reached state has auth enabled"); or drop the snippet's two
  panics (no Go user relies on them: `addSubstream` only reads the outcome). I would add
  `registered → 0 ≤ s` (cheap, true) and drop the first panic.
* **`ReqCancel`**: relies on "nothing of the id after its cancel response" and "a canceled id is not
  reused". `wireStep` allows both (see F2). The snippet's `Specs:` line cites "the server's ... the
  send loop's `ids`", which no spec states. Fixed by F2's `retired`/`seen`.
* **`ReqWholeRevision`** (and `ReqFromStart`'s header check): `wireStep` lets *any* watch's response
  be fragmented (its fragment case does not look at the registration's `w.fragment`), so the first
  response with events of a non-fragment watch may carry one event (`ReqWholeRevision` panics), and an
  intermediate fragment's header is unconstrained (`ReqFromStart`'s `r.Header.Revision < last event`
  panic). The member fragments only ids with `fragment[id]` (`watch.go:480-489`), and every fragment
  has at least one event (`:645-651`). Restatement: in `wireStep`'s fragment case, `m.events ≠ [] ∧
  ∃ w p, st.reg m.watchId = some (w, p) ∧ w.fragment = true` (an intermediate fragment's header is
  the final one's too: `cur.Header = wr.Header`, `:635`, if a snippet needs it). Or make the snippets
  reassemble fragments as `ReqFragments` does.
* **`ReqProgress`**: dereferences `r.Header.Revision` of a `-1` response; `srvWireStep` allows
  `hdr = none` there (`P = 0`), a nil-pointer panic in the snippet. Also, `wireStep`'s fragment case
  admits an empty fragment of id `-1`, which the snippet's test (`len(r.Events) == 0 && !r.Created &&
  !r.Canceled`) takes as the progress with an arbitrary header. The member always sets a header
  (`newResponseHeader`, every response) and never fragments a `-1`. Restatement: `m.hdr ≠ none` for
  every response (one conjunct of `wireStep`, true of the member; the Go client ignores it, it uses
  `ensureWatchHeader`), plus the fragment restatement above; or the snippet uses
  `r.GetHeader().GetRevision()` and checks `!r.Fragment`.

## Second tier

* **F4. `ReqFragments`'s assumption is too weak.** A watch from `0` has `done = none`, floor `H`; a
  response may start at any `lo ≤ H + 1` (1b's floor semantics, `issues/etcd-watch-current-resume-past-event.md`),
  so an earlier write to `pfx` by its owner could be among the events. Assume "`pfx` was never
  written before" (or watch from a revision).
* **F5. Client-certificate authentication is not covered** (check (d)). `EtcdServer.AuthInfoFromCtx`
  (`etcdserver/v3_server.go:1206-1216`) falls back to `AuthInfoFromTLS` (the certificate's CN) when
  `ClientCertAuthEnabled` and the context has no token. `req/..._auth.md` item 1 and `srvCtxPrin`'s
  docstring say the result is `nil` or `who`'s user; with a CN user and `who = none` the member
  registers a watch that `σa.permits none …` does not justify. Nothing in `Spec/` or
  `notes/specs-only/` mentions `ClientCertAuthEnabled`. Either a configuration scope premise
  (`ClientCertAuthEnabled = false`, in `watchMemberAt_cfg` / 2e) or `srvCtxPrin` (2a/W0) defines the
  principal of a token-less TLS stream as its CN. Cross-batch (W0, 2a, 3d).
* **F6. `srvWireStep` is now `wireStep`.** With 1b's working-tree `wireStep`, the two agree
  case by case (the `-1` branch's text is identical, including the pending-fragment conjunct). Make
  `srvWireStep` an abbreviation of (or replace it by) `wireStep`; the header's "until then 2a's
  boundary cannot turn a `srvWireStep` into a `wireStep`", `sendLoop`'s and `watchServer.Watch`'s
  "1b's `wireStep` corrected" and the `req/` hand-off are stale.
* **F7. `srvWatchSend_send` gives back `wireWatchRespOwn p dq m` at the fraction given, own `1`
  included.** grpc-go documents that the message must not be modified after `SendMsg` (stats
  handlers may read it lazily; `watch.go:627-633` quotes grpc-go#5857 for exactly this). The handler
  never writes a response after sending it (fresh `wr`/`cur` each time), so it needs only a read-only
  share back: state the law at `DFrac.discard` (the handler persists first, `wireWatchRespOwn_persist`),
  or give back only a persistent share. 2a's `SendMsg` (`Spec/google_golang_org/grpc/Api.lean:541`)
  has the same shape: 2a's call.
* **F8. The wire-request scope (check (c)).** Needed: an explicit id reaches
  `issues/etcd-watch-id-reuse-stale-events.md` (queued events of the canceled watch flushed to the
  new one through `pending`, `watch.go:468-475`, `:571-581`), and a `nil` oneof reaches the
  `default:` branch, whose `Var "uv"` is unbound in the translation (confirmed:
  `Code/.../v3rpc.lean`, `recvLoop.impl`, the `Infof` call near line 5795). Establishable by the Go
  client: `toPB` (`client/watch.go:1081-1100`) never sets `WatchId`, every request has a non-nil
  wrapper and inner message, and `run`'s cancels (`:663-669`, `:707-712`) too. Not needed: the
  non-`nil` *inner* request (`c ≠ null` in `watchReqOwn_unfold`): Go `break`s and the translation of
  `if uv.CreateRequest == nil { break }` is fine; harmless while `WireWatchReq` has no constructor
  for it, but say it is the model's, not the code's. Clients outside the scope that the batch report
  should name: the grpc-gateway (`embed`'s JSON watch, forwards `watch_id`), grpcproxy with
  etcd-io/etcd#21880, the in-process `v3client` (uses clientv3: inside). Small: `notes/perennial-changes.md`
  calls it "a `select` case's variable"; it is a type switch's.
* **F9. `WatchInternal.lean`'s invariant text.** `ids` also gets `-1` after any refused `Created`
  (`watch.go:568-570` runs for `wid = -1`; harmless since `-1` bypasses the `ids` test); "`prevKV[id]`
  ... the registration's" needs F1's fix to be true.
* **F10. `isPkgInit` carries the interval lock's invariant** (`GetProgressReportInterval`'s sketch)
  and `WatchServer.WatchTriple` has no `isPkgInit` although `watchServer.Watch.spec` needs it:
  `watchServerAt`'s realization must hold `isPkgInit v3rpc` (persistent; `NewWatchServer` has it).
  Say so in the realization; the lock invariant should become a stated law (`v3rpc.init`), as the
  author's open question says.

## Checks that pass

(a) Paths of `recvLoop`/`sendLoop`, against `srvWireStep` (with F1–F3 aside):
* `Created` order: every create gets exactly one control response, in order (`:281-286`,
  `:314-319`, `:368-372`; `closec` ends the loop); the send loop sends control responses in FIFO
  order. A registered id is fresh and not `-1` (mvcc auto ids), header `Rev()` read after `Watch`
  (`H ≥ R`, events from `R + 1 ≤ H + 1`: `WatchPos.init 0 H`'s floor holds); refusals have id `-1`
  and a non-empty reason (the `s < 0` one, auth's `rpctypes` errors, mvcc's
  `ErrEmptyWatcherRange`); `verify.Assert` holds.
* Pending buffering and the drain: a response of an unannounced id waits in `pending` and is
  flushed right after its `Created` (no other channel read in between); a `-1` progress is never
  buffered and, being computed after the registration, follows the drained responses; one computed
  before reaches the client before the `Created` (the id not yet in `st.regs`): sound.
* Events: mvcc's responses (fresh `*Event` per watcher, `watcher_group.go:79-95`, `Kv` shared, only
  `PrevKv` written by v3rpc), whole revisions, `c' ≤ Revision` (notify `rev`, victims
  `minRev - 1`); filters (`filterFuncs` drop iff `WatchReq.keeps` fails).
* Progress: per-id and `-1` only if all counted watchers synced and `rev ≥ startRev`
  (`watchable_store.go:540-547`), so `c ≤ P` with `c = s - 1`; a compacted-but-uncanceled watcher is
  not in `synced` and blocks `-1`.
* Compaction: `minRev < compactRev` gives `done + 1 < cr`; the compaction ends the registration;
  later `Cancel` of it still answers (`ws.cancels` keeps it), a no-op in `st`.
* Cancel races: responses of `W` before its cancel response are steps of its registration; those
  taken after it go to `pending` and are never sent.
* Fragments: only with ≥ 2 events (so never a compaction or a `-1`), contiguous (one goroutine),
  each non-empty, all of `wr`'s fields copied (`:634-643`), `fragmentsOf` holds; `sendFragments.spec`
  is sound for any `m`.
* Close: after mvcc's `Close` no send on its closed channel (`Watch`/`Cancel` fail; `RequestProgress*`
  find no synced watcher, `progressIfSync` sends nothing on an empty map); `ctrlStream` closed only on
  the `errc` path after `recvLoop` returned; `closec` once.
* `GetProgressReportInterval`: `Int63n(interval/10)` needs `interval ≥ 10`; the sum stays below
  `2^63` under `progressIntervalOk`; `NewWatchServer` raises to 100 ms. The float division by
  `len(evs) = 0` (`:510`) is Perennial's `float64Div`, no panic.

(d) mvcc's `req/` items are statable and true of the code (fresh auto ids; per-watcher event facts;
`-1` over live watchers; nothing produced after `Cancel` returns, victims included, since
`cancelWatcher` waits for a victim batch in flight; `Close` and later calls; `Range` at
`ModRevision - 1 ≥ 1` since a revision-1 event is always a creation). Auth's: true except F5.

(e) Snippets provable: `ReqServeWatch`, `ReqInterval`, `ReqCompaction`, `ReqPermission`; `ReqFromStart`
apart from the fragment header (F3); `ReqPrevKV` from the spec, but the spec is F1-unsound;
`ReqFragments` with F4's assumption.

## Targets ranked by need of revision

1. `ApiWatch.lean` (`srvWireStep`, i.e. 1b's `wireStep` it now equals: F2, F3, F6; F5, F7).
2. `serverWatchStream__sendLoop.lean` / `recvLoop.lean` / `WatchInternal.lean`: F1 (unsound with
   `PrevKv` until the fork fixes the order), F9.
3. `examples/specreq/v3rpcwatch/protocol.go`: F3, F4.
4. `watchServer__Watch.lean`, `NewWatchServer.lean`: stale text (F6), F10.
5. `sendFragments`, `isWatchPermitted` (F5 aside), `close`, `newResponseHeader`, the interval
   functions, the filters, `IsCreateEvent`: sound as stated.

## Verdict

Not done. The handler's structure, the drain-before-`Created` argument and the mvcc/auth hand-offs
are sound and well sketched. But `prevKV`, now in scope, meets a real race in the Go code (F1: to
file, and fix in the fork or descope), and the wire contract is too weak for its own snippets and,
after the `-1` correction, for the Go client's broadcast (F2, F3). The fixes are small: stream-wide
id freshness and retirement, fragments tied to the watch's flag and non-empty, a header always present.
