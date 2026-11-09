# Batch 1b (the client's watch API): report

Author's report. Everything builds against W0's round-1 names (`etc/specs-build.sh` on the 40
modules below: OK); the snippets vet (`cd examples && go vet ./specreq/clientv3watch/`, gofmt clean).

## Files

| path | what |
|---|---|
| `Spec/go_etcd_io/etcd/client/v3/ApiWatch.lean` | the watch vocabulary: pure model, `watchStep`, the wire protocol `wireStep`, resources, the `Watcher` contract (`Watcher.*Triple`, filling W0's `watcherAt`), laws, gRPC slots |
| `Spec/go_etcd_io/etcd/client/v3/WatchInternal.lean` | internal vocabulary of `watch.go`'s goroutines (not client-facing) |
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
