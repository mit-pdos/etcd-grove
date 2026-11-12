# Batch 1b (the client's watch API): report

Author's report. Everything builds against W0's round-1 names (`etc/specs-build.sh` on the 40
modules below: OK); the snippets vet (`cd examples && go vet ./specreq/clientv3watch/`, gofmt clean).

## Files

| path | what |
|---|---|
| `SpecPlan/Spec/go_etcd_io/etcd/client/v3/ApiWatch.lean` | the watch vocabulary: pure model, `watchStep`, the wire protocol `wireStep`, resources, the `Watcher` contract (`Watcher.*Triple`, filling W0's `watcherAt`), laws, gRPC slots |
| `SpecPlan/Spec/go_etcd_io/etcd/client/v3/WatchInternal.lean` | internal vocabulary of `watch.go`'s goroutines (not client-facing) |
| client-facing specs (10) | `watcher__{Watch,RequestProgress,Close}`, `Client__{Watch,RequestProgress}` (promoted), `NewWatcher`, `NewWatchFromWatchClient`, `WatchResponse__{Err,IsProgressNotify}`, `ensureWatchHeader` |
| internal specs (28) | `valCtx__{Deadline,Done,Err}`, `streamKeyFromCtx`, `watchRequest__toPB`, `progressRequest__toPB`, `watcher__{newWatcherGRPCStream,closeStream}`, `watchGRPCStream__{close,run,nextResume,addSubstream,dispatchEvent,broadcastResponse,unicastResponse,closeSubstream,sendCloseSubstream,serveWatchClient,serveSubstream,startBufWait,recordBufWait,newWatcherStreamBufLogger,newWatchClient,waitCancelSubstreams,joinSubstreams,backoffIfUnavailable,openWatchClient}`, `watcherStream__resetBufWait` |
| `examples/specreq/clientv3watch/{history,progress,ending,consume}.go` | 15 requirement snippets |

Every function of `watch.go` has a spec (all were proved before). W0 already owns `OpWatch`,
`WithRev`/`WithPrefix`/`WithPrevKV`/`WithProgressNotify`/`WithCreatedNotify`/`WithFilter*`/
`WithFragment`/`WithRequireLeader`, `Op.IsProgressNotify`.

## Exported vocabulary (`ApiWatch.lean`, namespace `ClientV3`)

Pure: `WatchReq` (range normalized as the member does, `prevKV`, filters, notify flags,
`fragment`), `OpM.watchReq`, `OpM.watchRev`; `WEv`, `WEv.ofEvent`, `WatchReq.keeps`,
`watchEvents w h lo hi` (the range's filtered events of revisions `lo..hi`), `WatchReq.prevOk`;
`EventM`, `EventM.isOf`; `WatchRespM` (exported fields + `closeErr` kind), `.isErr`,
`.isProgressNotify`, `.hdrDq`; `WatchPos` (`done : Option Nat`, `started`, `ended`), `WatchPos.init`;
**`watchStep who w σ σa p m p'`**: what a response says (errors end the watch; compaction:
`cr ≤ σ.kv.compacted`, `done + 1 < cr`; `Created` only first and only with `createdNotify`; events:
exactly `watchEvents` from `done + 1` to the last event's revision, whole revisions, the principal
permitted at `σa`; progress at `P`: no event in `(done, P]`, `done ≤ P`).
Wire (contract with 2a/2b/3h): `WireWatchReq`, `.creates`, `WireWatchRespM`, `.toResp`,
`HeaderM.zero`, `WireSt`, `.reg`, `.setReg`, **`wireStep`** (creates answered FIFO, per-id
`watchStep`, id `-1` progress for all, cancel, fragments).

Resources: `watcherHandle w γ who` (persistent), `watchChAt ch γ who w p` (the consumer, exclusive),
`watchRespAt v m` (exclusive), `eventOwn p dq e`, `closeErrOk e k` (persistent); slots
`remoteWatchAt`, `WatchStreamNames`, `wireWatchSend`, `wireWatchRecv`, `wireWatchSentLb`,
`watchReqOwn`, `wireWatchRespOwn`.

Contracts: `Watcher.WatchTriple f P γ who`, `Watcher.RequestProgressTriple f P who`,
`Watcher.CloseTriple f P`.

Laws: `watch_persistent`, `watcherAt_methods` (W0's slot's meaning), `watcherHandle_watcherAt`,
`watchChAt_recv` (receive / `for range`), `watchChAt_recvAu` (a `select` case, Perennial's
`recvAu`), `watchRespAt_fields`, `eventOwn_unfold`, `closeErrOk_nil`, `remoteWatchAt_watch`,
`wireWatchSend_send`, `wireWatchSend_lb`, `wireWatchRecv_recv`.

Internal (`WatchInternal.lean`): `RunM`, `WsM`, `wgsAt`, `wgsRun`, `wgsSend`, `wgsRecv`,
`wgsDoneTok`, `wsAt`, `wsOwn`, `wsServe`, `wsClosed`, `wsCloser`, `deliverOk`, `wcsPending`,
`wcsStop`, `nowFuncOk`, `initReqAt`, `bufLoggerAt`; laws `watchInternal_persistent`,
`valCtx_ctxOk` (a `valCtx` is a never-done `ctxOk` context keeping `ctxPrin`),
`watchRespAt_noEvents_dup`, `wcsPending_close`, `wcsPending_join`.

## Main changes from the old specs

* **Responses are persistent facts about the history, not firings of a read update** (old D47:
  `□ AU` fired per response, `watchStateElem`, a `monoList` cursor). With W0's whole-history model
  each response carries `etcdLb γ σ` and the pure `watchStep`; no `Q`, no `kvRoom`, no cursor ghost
  name in the client's statement (the position is a pure index of `watchChAt`).
* **Relaxed**: any range (was a non-empty prefix; the empty key normalized), any start revision
  (`0`, negative; was `≥ 1`), any context (`ctxOk` + W0's `ctxPrin`; was `watchCtx`), filters,
  `prevKV`, fragments, `createdNotify`, progress, compaction; auth in every mode and any number of
  members (the admitting state `σa`, replacing the one-member gate `watchCheckOk` and
  `authPubLbM`); no `watchSizeOk`, no `srvNoDupKeys` (a key written twice in a revision gives both
  events, as the history has them), no `WEnv`.
* **No thread token**: the goroutines `Watch` starts come with their own (`wp_fork_tok`).
* Consumers own responses in full (Election.Observe writes `Header.Revision`; the namespace
  wrapper and Kubernetes rewrite events), except a broadcast progress's shared header (read-only).

## Functions left out

None of `watch.go`. `isHaltErr`, `isUnavailableErr` (`client.go`) and `newBlockLogger`,
`blockLogger.recordWait` (`block_logger.go`) are 1c's (requested in `req/go_etcd_io_etcd_client_v3.md`).

## Findings in the Go code (not filed: outside my paths; for the coordinator)

1. **A watch from the current revision (`rev = 0`) can lose or add events across a reconnect**
   (`client/v3/watch.go` `serveSubstream`: `nextRev = wr.Header.Revision`, the creation header's
   `H`, read by the member after registering the watch at `H' ≤ H`): if the stream fails before
   any event, the resume from `H` (a) delivers revision `H`'s events, which precede the watch when
   `H' = H`, and (b) skips events of revisions in `(H', H)` when writes landed between the
   member's registration and its header read; (c) with `WithProgressNotify`, a progress tick in
   that window gives a progress `P < H` that the client delivers, and the resume from `H` then skips
   events in `(P, H)` after the consumer was told it had everything up to `P`. Narrow windows; no
   test written. The spec states it: a `rev = 0` watch's position is unknown until its first event
   (`WatchPos.init 0`), and a progress does not fix it. No user found relies on `rev = 0`
   completeness (every user passes `WithRev`). Candidate `nonissues/` (or an issue with a test).
2. **grpcproxy's broadcast advances `nextrev` to `Header.Revision + 1` after every response**
   (`server/proxy/grpcproxy/watch_broadcast.go` `bcast`), but an unsynced watcher's batch is cut at
   1000 revisions with the header at the store's current revision (`mvcc/watchable_store.go:397-401`):
   a receiver added afterwards (`add`: `wb.nextrev > w.nextrev` check) may be told it is caught up
   past events it will never see. Not verified (grpcproxy is no batch's); a lead.

## Decisions for the user

1. **Watch responses as `etcdLb` facts, no atomic update** (above). The old `□ AU` form is
   stronger only in letting a client's invariant act at the moment of each response, which no user
   needs (nothing to linearize: a watch reports the past).
2. **`rev = 0` watches**: completeness only from the first event (finding 1). Alternative: fix
   the client (resume from `H + 1` is not right either; the member would have to return its
   registration revision) and state "complete from the member's revision at creation".
3. **`Created` and progress are facts, not promises**: that a `Created` or progress response comes,
   or that a channel closes when its context ends, is liveness and unstated.

## Open questions

1. W0: move the watch messages (`EventM`, `WireWatchRespM`, `WireWatchReq`, `eventOwn`,
   `watchReqOwn`, `wireWatchRespOwn`) into `api/v3/Wire.lean`? (`req/go_etcd_io_etcd_api_v3.md`.)
2. W0/user: a compaction retention in `EnvCfg` for `examples/etcd/compactwatch` (its panic on
   `Get.rev < CompactRevision + retention`); otherwise that example's check is unprovable.
3. `deliverOk` and the internal wire tie are coarse: the internal specs mirror the code at the
   level of `run`'s model (`RunM`); the integration round should check them against 2a/2b's final
   stream specs.

## `req/` sections written (`## from 1b`)

`google_golang_org_grpc.md` (bidi stream: open, send, receive with facts, errors classified, no
size premise, metadata/status helpers); `go_etcd_io_etcd_server_v3_etcdserver_api_v3rpc.md` (2b: the
Watch handler's protocol `wireStep`: FIFO creates, permission at create, whole revisions, progress
not below the position, compaction, cancel, fragments); `go_etcd_io_etcd_api_v3_etcdserverpb.md`
(stub `NewWatchClient`, the watch messages' predicates, getters); `go_etcd_io_etcd_api_v3_v3rpc_rpctypes.md`
(`rpctypes.Error` on close errors, `ErrCompacted`/`ErrFutureRev`); `go_etcd_io_etcd_client_v3.md`
(1c: `GetLogger`, `isHaltErr`/`isUnavailableErr`, the block logger, `Client.Close`; principal via
`ctxPrin`); `context.md` (W0: `WithCancel` over a `ctxOk` parent, `Done` in a `select`: now covered
by W0's round 1); `go_etcd_io_etcd_api_v3.md` (W0: the watch messages' home, the retention).

## Round 1 repairs (2026-11-09)

Reviews: `reviews/1b-provability-1.md` (P), `reviews/1b-completeness-1.md` (C). All first-tier
findings fixed or answered; the 40 modules build, the snippets vet.

| finding | repair |
|---|---|
| P-F1, C-F1 (compaction with `closeErr`; anything after an error) | `watchStep`'s error case: `closeErr ≠ none → compactRev = 0 ∧ header 0`, `compactRev ≠ 0 → closeErr = none ∧ …`; the ended case: only `closeErr` responses (header `0`, no compaction, no events) |
| P-F2 (`Err` on a `closeErr`) | `WatchResponse.Err.spec`'s `some` case gives `err ≠ nil` |
| P-F3 (progress `P` vs the Go header) | `sint.Z m.hdr.revision = P`; also `sint.Z m.compactRev = cr`; `wireStep`'s `-1` case the same |
| P-F4 (fragments of another id) | `WireSt.frag : Option (Int × List EventM)`; a pending fragment forces the next response's id, no creation or cancel; the odd conjunct dropped; 2b's req updated |
| P-F5 (`deliverOk` for `Created`s run dispatches) | `deliverOk s γ who (tgt : Option Int) m` (`none`: broadcast); realization restated: an unregistered id needs nothing, a `Created` is forwarded only with `retc` pending and `createdNotify`, else dropped; `dispatchEvent`/`broadcastResponse`/`unicastResponse` updated |
| P-F6 (`ReqWatchRefused` vacuous) | snippet dropped, recorded in `ending.go` and below (open question 4); the event case's `σa` documented as any reached state (a lagging member's applied auth) |
| C-F2 (read-only responses, 1g's request) | `watchRespRO` (persistent), `watchRespAt_persist`, `watchRespRO_persistent`, `eventOwn_persist`; snippet `ReqWatchShare` |
| C-F3 (`rev = 0` completeness) | `WatchPos.floor`: `Watch`'s post gives `WatchPos.init rev r0` with `etcdLb γ σ0`, `r0 = σ0.kv.rev`, or `WatchPos.closed` (a channel that ends at once); the event case at an unknown position has `lo ≤ floor + 1`; `wireStep` registers a start-`0` watch with the `Created` header as floor; snippet `ReqWatchFromNow` |

Second tier: S1/S2 (P) stated in `WatchInternal.lean`'s header (the tie is a refinement; `ws.id`
is `run`'s; `initReq.rev` split by fraction); S4 (P) `watchReqOwn`'s create key (`""` for
`"\x00"`), 3h's req; S6 (P) `watcher.Watch`'s margin reworded; `Watch` returns `⌜ch ≠ null⌝` (1f);
1d told in `req/go_etcd_io_etcd_client_v3.md` that non-decreasing headers are false of the code
(with the case); C-S2 `ReqWatchChained`; C-S3 `ReqWatchOptions` (`WithRequireLeader`, `WithRange`,
empty key with prefix, `WithWatchBufLog`); C-S6 snippet headers (`waitDelete` watches from the Get's
revision), `ReqWatchPrevKVCompacting` (Kubernetes' pattern under compaction); `watcher.Watch`'s
Users add grpcproxy's coalescing and health check; P-S5 asked of W0 (now `etcdLb_revFits`).

**Go finding filed**: `issues/etcd-watch-current-resume-past-event.md` with
`issues/etcd-watch-current-resume-past-event/watch_current_resume_test.go`, failing at
etcd-io/etcd@ea8b5943 (one member behind a bridge: put, watch from now, drop connections: the put
is delivered). `blocks-proof: no`; `issues/INDEX.md` regenerated (`etc/issues-status.py --index`).
The racy parts (a skip in `(R, H)`, a progress below `H`) are noted in it, not reproduced. My
earlier grpcproxy lead (finding 2) is withdrawn: C-S7's reading is right (the receiver's own
`nextrev` filter drops what is below its start, and later responses carry the rest).

**Known unserved users (C-S4, outside every batch)**: `v3client`'s `watchWrapper` (`blankContext`:
needs `ctxOk`/`ctxPrin` of it, 1c/W0), grpcproxy forwarding a downstream token (excluded by
`ctxPrin`), the namespace wrapper as a client's `Watcher` (keys stripped: not `watcherAt` for `γ`).

**Open question 4 (new) for the user**: a refused watch delivers nothing only on an up-to-date
member. `examples/etcd/auth/authkv.go:272` relies on it with one member. Options: (a) a lower bound
on the admitting state for a one-member cluster, taken at the call (`σ.members.length = 1 → Reach
σ₀ σa`), one spec; (b) keep the spec as is and record that authkv's check rests on its single
member (done for now).

## Round 1b: 2b's correction of `wireStep` (2026-11-09)

Adopted as 2b asked (`req/go_etcd_io_etcd_client_v3.md`, "from 2b"): in `wireStep`'s id `-1`
case a registration whose cancel request is in `ss` is exempt (no claim, position kept). Checked:
the member's `recvLoop` runs mvcc's `Cancel` before queueing the cancel response, and `sendLoop` may
send a later progress first (`v3rpc/watch.go:374-402, 514-546`); the client sends a cancel only for an
id with no substream (`closeSubstream` removed it, or an unknown id), and `broadcastResponse` reaches
only `w.substreams`, so no consumer is told anything less (`deliverOk`'s header says so). `srvWireStep`
(2b) and `wireStep` now agree.

## Round 2 (from 2b) (2026-11-09)

Strengthenings of `wireStep` that 2b's reviews asked for (`2b-provability-1.md` F2/F3,
`2b-completeness-1.md` F1/F2), checked against `v3rpc/watch.go`:

1. **Ids**: `WireSt.seen` (ids announced by a `Created`) and `WireSt.retired` (ids whose cancel
   response was sent). A registration's id is not in `seen`; a cancel response's and any other
   response's id is in `seen` and not in `retired` (mvcc's ids only grow, `:468-474`; after a cancel
   response the id leaves `ids`, so a late response of it stays pending and is never sent,
   `:564-566`). The client's `run` sketch is unaffected (its broadcast reaches `w.substreams` only).
2. **Negative start**: a create with a negative start revision is refused (`:272`); a registered
   watch has a non-negative start.
3. **Fragments and headers**: a fragment has at least one event and is of a registered watch with
   `Fragment` set; every response has a header.
4. **`PrevKv` window** (2b's finding: `sendLoop` reads `prevKV[id]` at `:443-445` before `recvLoop`
   sets it at `:342-349`): `WatchReq.prevOk` takes `loose`; `WatchPos.prevLoose` is true at a
   registration and may turn false once (the responses built after the flag was set; the pending
   ones flushed after `Created` form a prefix), never back. A client's channel keeps it true (every
   reconnect re-registers), so a consumer gets: a non-`nil` `PrevKv` is the previous record, a `nil`
   one says nothing. The no-compaction `prev-kv` snippet is dropped (false of the code: recorded in
   `consume.go`); `ReqWatchPrevKVCompacting` (Kubernetes' pattern: `nil` is an error) stays true.

Also: W0's `ctxPrin dflt ctx p` (a per-call principal) adopted: `Watcher.WatchTriple` and
`RequestProgressTriple` take `∀ p, ctxPrin who ctx p`, and the consumer's facts are `p`'s;
`remoteWatchAt_watch` the same; `valCtx_ctxOk` keeps `ctxPrin`; a stream's internal predicates
are indexed by its own principal (`newWatcherGRPCStream`, `closeStream`). My 40 modules build; the
directory's other failures are 1c's in-progress `authClient__*` (`Auth.Triple`).

## Round 3 (compaction exactness) (2026-11-09)

3f showed mvcc's events are exact only under the user's round-11 condition (a compaction keeps a
key's last change of a revision that changes it twice; through gRPC such a revision comes from
`issues/etcd-txn-check-intervals-sibling.md`). Chosen form, matching 3f's `wStep` and the approved
example's single condition (no disjunction): **the guarantee is gated**, not the create.
`ClientV3.exactFrom h lo` (`ApiWatch.lean`, stated once; 2b and 3f cite it): every revision from
`lo` up to `h.compacted` changes each key at most once. In `watchStep`, an event response's
exactness (`Forall₂ … watchEvents`) and a progress's "no events" hold under `exactFrom σ.kv (done + 1)`
(`lo` for the events); the rest (last revision past the position and reached, `P ≥ done`, the
compaction case, permission) is unconditional; `wireStep`'s `-1` progress the same. Snippets: the
package comment adds the condition to the owner's invariant (a workload with no transaction that
puts and deletes one key, or no compaction); `order`, `filter`, `select`, `rewrite` and the history
snippets cite it; `compacted`, `ends`, `created-first`, `close`, `share`, `options`,
`request-progress` need none. 3f may replace its `exactFrom` by this one (same body).

## Round 4 (compaction after restore) (2026-11-09)

3f's review F1: the member compares a compaction against the watcher's `minRev`, which a progress
never raises and a snapshot `Restore` keeps (`watchable_store.go:483-503, 528-554, 215-219`), so
after a restore a watch told "nothing up to `P`" may be canceled at `cr ≤ P`. `WatchPos` gains
`evDone` (the last event's revision, or the start's - 1; raised by event responses only, kept by
progress, errors and `Created`); the compaction clause of `watchStep` (hence `wireStep`'s per-id
case) is now `∀ c, p.evDone = some c → c + 1 < cr`. On the client a resumed registration starts at
`nextRev ≥ evDone + 1`, so the member's `minRev` is still above `evDone`. `ReqWatchCompacted`
(`cr > rev`) still follows (`evDone ≥ rev - 1`); no snippet relied on a progress there.
