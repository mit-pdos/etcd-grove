# Batch 2b: etcd's gRPC watch service (`server/etcdserver/api/v3rpc/watch.go`)

Author's report (round 0, before review). Every file builds (`etc/specs-build.sh --dir
Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc`: OK, 16 modules); the snippets vet
(`cd examples && go vet ./specreq/v3rpcwatch/`).

## Files

| file | what |
|---|---|
| `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/ApiWatch.lean` | the vocabulary (namespace `V3rpc`): the contract `srvWireStep`, pure helpers, `watchServerAt`, `watchServiceAt` and the handler contract `WatchServer.WatchTriple`, the member slot `watchMemberAt`, the server end of a stream (2a's slots), laws, laws offered on 1b's message slots |
| `.../v3rpc/WatchInternal.lean` | internal: one handler run (`swsAt`, `swsRecver`, `swsSender`, `swsCloser`), the run's invariant described |
| client-facing specs (2) | `NewWatchServer`, `watchServer__Watch` |
| exported helpers (6) | `FiltersFromRequest`, `filterNoPut`, `filterNoDelete`, `IsCreateEvent`, `GetProgressReportInterval`, `SetProgressReportInterval` |
| internal specs (6) | `serverWatchStream__{recvLoop,sendLoop,isWatchPermitted,close,newResponseHeader}`, `sendFragments` (new: no old spec; `sendLoop`'s sketch needs it) |
| `examples/specreq/v3rpcwatch/protocol.go` | 9 snippets over a raw `pb.WatchClient` stream: `ReqCreatesInOrder`, `ReqFromStart`, `ReqWholeRevision`, `ReqProgress`, `ReqCancel`, `ReqCompaction`, `ReqPrevKV`, `ReqFragments`, `ReqPermission` |
| `examples/specreq/v3rpcwatch/serve.go` | 2 snippets: `ReqServeWatch` (registration), `ReqInterval` |

No function of `watch.go` is left out (every translated one has a spec; `sendWatch` is a closure of
`sendLoop`). `isClientCtxErr` and the metrics are names only in the translation (2a's, ambient).

## Exported vocabulary (`ApiWatch.lean`)

Pure:
* `srvWireStep who σ σa ss st m st'`: **the contract**: 1b's `wireStep` (the client's wire protocol)
  except that a progress of id `-1` exempts registrations whose cancel request the member had read
  (they keep their position). See "Findings" 1.
* `progressIntervalOk d` (`10 ≤ d ∧ d + d / 10 ≤ 2 ^ 63`: the interval lock's invariant),
  `watchIntervalCfgOk d` (the configured interval: `≤ 0`, or raised to 100ms within the former),
  `minWatchProgressIntervalNs`, `filterNoPutTy`, `filterNoDeleteTy`, `filterFuncs fl` (the filter
  functions of the filter types), `fragmentsOf m ms` / `fragPrefix m ms` (how `sendFragments` cuts a
  response), `createRange k e` (a create's range: empty key `"\x00"`), `watchSrvStreamTy`.

Resources (all opaque):
* `watchServerAt p γ` (persistent): a `*watchServer` of a member of `γ`.
* `watchServiceAt v γ` (persistent): the `pb.WatchServer` value serves `γ`'s watch protocol; meaning
  `watchServiceAt_methods` (`WatchServer.WatchTriple`); `watchServerAt_service` for a `*watchServer`.
  The slot 2a's registration consumes.
* `watchMemberAt s γ` (persistent): **slot of 2c/2d/2e**: the started member `s`; law
  `watchMemberAt_cfg` (its configuration's logger, request budget, interval read-only, the interval
  with `watchIntervalCfgOk`); its other triples in `req/` (below).
* **2a's slots, the server end of a watch stream**: `srvWatchStreamAt st γ who g` (persistent),
  `srvWatchRecv st g rs` (exclusive), `srvWatchRecvdLb g rs` (persistent), `srvWatchSend st γ who g
  sst` (exclusive), `srvCtxPrin ctx who` (persistent). Laws: `srvWatchStreamAt_context`,
  `srvWatchRecv_recv`, `srvWatchRecv_lb`, `srvWatchRecvdLb_sent` (to 1b's `wireWatchSentLb`),
  `srvWatchSend_send` (a response with its `srvWireStep` facts), `watch_srv_persistent`.
* Laws on 1b's message slots, offered to their realizer (3h): `watchReqOwn_unfold`,
  `wireWatchRespOwn_unfold`, `wireWatchRespOwn_persist`.

Internal (`WatchInternal.lean`): `swsAt sws γ who st g` (persistent), `swsRecver sws rs`,
`swsSender sws`, `swsCloser sws`; `swsAt_persistent`.

## Main changes from the old specs (`specs-ref`)

* **The contract is the client's wire protocol.** The old handler spec was over a server-side
  stream specification (`srvStreamIs … Up Dn`, `watchStreamSpec γs R W tok Dn`, `watchDn`, the
  auxiliary name, the auth mode's tag); now every response the handler sends carries 1b's
  `wireStep` facts (corrected: `srvWireStep`) through 2a's `srvWatchSend_send`, read against
  `etcdLb γ σ` / `etcdLb γ σa`: one model for both ends.
* **Relaxed scope**: `prevKV`, fragments and filters are in scope (the old `watchReqOk` excluded
  them); auth on and off in one statement (the permission at a reached state `σa`, no mode tag, no
  published-index bound `n`, no `classResFrom`/`principalBoundI`); compaction (1b's compaction
  case); any number of watches, cancels, progress requests.
* **No implementation vocabulary in the statements**: the server's internals (`watchSrvOk s E tag`,
  `srvKVAddr`, `srvIdsOk`, the run record `WRun`, the answer pool, the control producer token, the
  close token, mvcc's `wsRecv`/`mvccReaders`) replaced by `watchMemberAt s γ` (exported) and the
  run's shares (internal).
* **Bounds**: no reader resources or `threadBound` premises; the loops take their goroutines' thread
  tokens (the store's and the auth store's reader slots, the interval lock's, `sws.mu`'s); the
  handler takes none (its goroutines get theirs from `Fork`).
* **The interval**: `SetProgressReportInterval`'s premise relaxed from `10 ≤ d ≤ 2 ^ 62` to what the
  code needs (`progressIntervalOk`); `NewWatchServer`'s `d ≤ 2 ^ 62` became the configuration's
  `watchIntervalCfgOk`, inside the member slot (2e takes it where it is configured).
* `FiltersFromRequest`'s post gives the exact functions (`filterFuncs`), so mvcc can be given each
  filter's contract; `filterNoPut`/`filterNoDelete`/`IsCreateEvent` over the event's fields (mvcc's
  events own their struct but share their `Kv`).

## Findings

1. **1b's `wireStep` is false of the member for progress of id `-1` after a cancel** (code reading,
   `watch.go:374-402`, `:514-546`): a client that cancels an unsynced watch `W` and then requests
   progress can receive the progress at `P` before `W`'s cancel response, while `W`'s events below
   `P` are never sent (mvcc's `RequestProgressAll` no longer counts `W`; `sendLoop`'s `select` takes
   the mvcc channel before the control channel). The Go client never delivers that progress to `W`
   (it removes a closing substream before sending its cancel), so this is not a user-visible bug of
   etcd's client; a raw client that trusts a progress for a watch it canceled would be misled.
   **Repair asked of 1b** (`req/go_etcd_io_etcd_client_v3.md`, `## from 2b`): exempt the
   registrations whose cancel request is in `ss`. 2b states `srvWireStep` meanwhile; 2a's boundary
   composes only once 1b adopts it. For the coordinator: a `nonissues/` entry (documentation of the
   progress response vs. canceled watches; no Go test written).
2. **Translator bug** (still present at the pin): `recvLoop`'s `default:` branch reads the type
   switch's `uv`, unbound there in the translation (`Code/.../v3rpc.lean`, `recvLoop.impl`): the
   branch is stuck in the model (harmless in Go). It forces the wire-request scope (decision 1) for
   empty or unknown oneofs. For `notes/perennial-changes.md` (outside 2b's paths): Goose should bind
   a type switch's variable in `default:` to the switched value.

## Decisions for the user

1. **The stream's clients send wire requests** (`WireWatchReq`, through 1b's `watchReqOwn`): a
   create asks for no watch id of its own (`WatchId = 0`), no request is an empty/`nil` oneof. etcd's
   Go client meets it (`toPB`). Why: an explicit id may reuse a canceled watch's id and receive its
   queued events (`issues/etcd-watch-id-reuse-stale-events.md`, a real bug: no true contract gives
   such a client the protocol), and the translator bug above. The cost: the server's contract says
   nothing for other clients (grpc-proxy, the gateway, a raw client choosing ids). Alternatives: a
   weaker contract for explicit ids (fresh ids only, a premise "never reuse a canceled id") — a
   second mode in `srvWireStep`, for clients nothing in scope has; and the Perennial fix for the
   `default:` branch (general, its own review).
2. **`watchIntervalCfgOk`** (the progress interval at most about 265 years) as a configuration scope
   premise of `NewServer` (`nonissues/etcd-watch-progress-interval-overflow.md`: the user's 2026-10
   "skip"). Kept, as tight as the code.

## Open questions

* **2a's server-context principal**: 2b defines `srvCtxPrin ctx who` (what `AuthInfoFromCtx`
  consumes); if 2a defines one for the unary handlers (W0's item 6), 2b switches to it.
* **`watchMemberAt`'s method triples** (`Cluster().ID()`, `MemberID()`, `Watchable()`, `Term()`,
  `Leader()`, `AuthInfoFromCtx`, `AuthStore()`) are stated in prose (`req/`), the mvcc stream's and
  the auth store's contracts too: their vocabularies (3f, 3d, 2c) do not exist yet. The integration
  round should state them as laws of `watchMemberAt` over those batches' predicates.
* **v3rpc's package initialization** (shared with 2a): `isPkgInit` must carry the interval lock's
  invariant (`progressIntervalOk progressReportInterval`; the initializer's 10 minutes meets it).
* Ambient libraries the sketches call, assumed panic-free: prometheus metrics
  (`streamFailures`, `watchSendLoop*`), the otel tracer (`traceutil.Tracer.Start`,
  `trace.WithAttributes`, `attribute.*`), `verify.Assert` (true condition), `math/rand.Int63n`
  (positive bound), zap.

## `req/` sections written

* `req/go_etcd_io_etcd_client_v3.md`, `## from 2b (to 1b: a correction of wireStep)`.
* `req/google_golang_org_grpc.md`, `## from 2b`: the server end of a watch stream (registration,
  `Recv`, `Send` with facts, `Context`, error helpers, `proto.Size`).
* `req/go_etcd_io_etcd_server_v3_storage_mvcc.md` (new file), `## from 2b`: the watch stream
  (`NewWatchStream`, `Watch` with fresh auto ids, the channel's facts per watcher and for id `-1`,
  `Cancel`, `RequestProgress*`, `Rev`, `Close` without sends after, `Range` for `prevKV`).
* `req/go_etcd_io_etcd_server_v3_auth.md` (new file), `## from 2b`: `AuthInfoFromCtx`,
  `IsRangePermitted` at a reached state.
* `req/go_etcd_io_etcd_server_v3_etcdserver.md`, `## from 2b`: the `watchMemberAt` slot.
* `req/go_etcd_io_etcd_api_v3_etcdserverpb.md`, `## from 2b`: the message laws.
