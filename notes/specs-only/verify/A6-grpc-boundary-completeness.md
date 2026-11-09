# A6 (gRPC boundary): completeness verification

Reviewer: completeness kind, independent. Area: batches 2a (v3rpc without `watch.go`, grpc, proto,
rpctypes), 2b (v3rpc's watch server), 3h (etcdserverpb, version), with net/http (2f's vocabulary,
in this area's directories). Commit under review: `1aa6fc1337` (`specs-only`). I wrote the findings
before I read `batch-*.md`, `integration-*.md` and `open-questions.md`. I read them afterwards only to
mark the findings that are already recorded.

Go sources: `.lake/src/{server,client,api}` (a4d2bb17), tests
`~/go/pkg/mod/github.com/upamanyus/etcd/tests/v3@…a4d2bb1720b9`, Kubernetes
`~/go/pkg/mod/k8s.io/apiserver@v0.0.0-20261021221356-9c4ec15b8038`, grpc-go v1.84.0.

## Verdicts

| batch | verdict |
|---|---|
| 2a (v3rpc unary, grpc, proto, rpctypes) | **FAIL**: F2, F3, F4, F6a |
| 2b (v3rpc watch) | **PASS WITH OPEN DECISIONS**: the in-process client's watches (open-questions 1.5) and the scope of wire requests (3.8) |
| 3h (etcdserverpb, version) | **FAIL**: F1 (the part about the 11 auth stubs and handlers is not recorded; the rest is open-questions 7.4), F6b |

net/http (2f's vocabulary): I found no completeness gap for its users in this area (rafthttp,
`leasehttp.RenewHTTP` (trusted), `etcdstart`'s `http.Serve`). `leasehttp`'s server handler
(`http.MaxBytesReader`, `lease/leasehttp/http.go:65`) has no spec, but it is out of scope as
`RenewHTTP.lean` records.

## Counts

- Specs: 283 files, 474 `.spec` obligations (handler triples, stubs, boundary specs and laws).
  - Coverage against `specs-ref`: all 87 old v3rpc specs are here, and both version specs.
  - Old grpc, proto and etcdserverpb specs not here: 32 files.
  - 25 of those are covered another way:
    - the 7 `Generic{Client,Server}Stream__*` specs are the laws `genCli_*`/`genSrv_*`;
    - the 18 per-type proto variants (`MarshalPb`, `CloneConfState`, `UnmarshalRole`, ...) are the
      generic `Proto.{Marshal,Unmarshal,Clone,Equal,Size,Merge}.spec` over `msgAt`.
  - **7 are dropped (F6).**
- Snippets: 31 (`v3rpc` 6, `grpc` 3, `v3rpcwatch` 14, `etcdserverpb` 8).
  - 30 rely on what their users rely on, and their specs exist.
  - `v3rpc/range-stream` calls a stub that has no spec (F1).
- Users:
  - I classified 15 patterns (below), with one real call site each.
  - 9 close.
  - 3 are blocked by an unrecorded finding (F1-auth, F2, F3/F4).
  - 3 are recorded open decisions or scope restrictions (the in-process client, the TLS+HTTP path,
    cmux/gateway).
- Callers' specs in other areas that use this area: checked those of client v3 (1c/W0), txn (3b),
  v3election (2e) and leasehttp.
  - Every Lean name resolves: the build passes, and I checked every `Grpc.`/`EtcdServerPb.`/`V3rpc.`/
    `Rpctypes.`/`Http.`/`Proto.` citation in comments and snippets.
  - These sketches cite specs that do not exist: F1, F3, F6.

## User patterns

| # | pattern (call site) | covered by | closes? |
|---|---|---|---|
| P1 | build and serve a member's gRPC server (`examples/lib/etcdstart/common.go:193-201`, `cluster3.go:119`) | `Server.spec`, `Grpc.start/Serve/GracefulStop` | yes, except for the untranslated handlers (F1) |
| P2 | embed: register election/lock on that server (`server/embed/serve.go:184-186, 244-246`) | nothing | **no (F4)** |
| P3 | embed: TLS+HTTP path through `grpcHandlerFunc` (`serve.go:258-261`), and cmux (`serve.go:141, 211`) | `startHTTP`, `cmuxSubAt` | recorded open (3.7; cmux in `Grpc/Api.lean`) |
| P4 | client KV unary through stubs (`client/v3/retry.go`) | `NewKVClient`, `kVClient.*`, `attemptOk_call`, `etcdUnary` | yes |
| P5 | client RangeStream (`retry.go:111-112`; Kubernetes `store.go:951`; tests `kvc.RangeStream` ×5) | none for the stub | **no (F1, recorded 7.4)** |
| P6 | client Lease/Watch streams and unary calls | `leaseClient.*`, `watchClient.Watch`, `kaSpec`, `watchSpec` | yes |
| P7 | client Auth/Cluster/Maintenance unary calls (`retryAuthClient`, `retryClusterClient.*`, `retryMaintenanceClient.Alarm`) | 6 of 17 auth stubs; no cluster or maintenance stub | **no (F1)** |
| P8 | error classification (`rpctypes.Error`, `ErrorDesc`, `status.FromError/Code`, `EtcdError.Code`; Kubernetes `errors.go:33,54`, `metrics.go:229-234`) | rpctypes `init.spec` (table checked against `error.go`: 63/63 descriptions, codes and the `errStringToError` key set match), `Grpc.status*` | yes |
| P9 | Kubernetes `status.Code(err) == Unimplemented` on stream errors (`store.go:956-959`, `watcher.go:316,397`) | `status.Code.spec`; fallback is safe either way | yes |
| P10 | the client's `Config.DialOptions` from Kubernetes (`storagebackend/factory/etcd3.go:309-339`) | `dialOptsOk` (slot, only `dialOptsOk_nil`) | **no (F2)** |
| P11 | `grpc.Peer(&p)` and `p.String()` in the retry interceptor (`client/v3/retry_interceptor.go:46-47, 71`); `peerInfo.Addr.String()` (`v3rpc/interceptor.go:106`) | `Grpc.Peer.spec`, `peer.FromContext.spec` | **no (F3)** |
| P12 | outgoing and incoming metadata (client `WithRequireLeader`, token; server interceptors and auth) | `metadata/*`, `outMD_*`, `ctxInMD_*`, `mdPrin_of`, `reqPrin_of_md` | yes |
| P13 | in-process client `v3client.New` over the handlers (`v3client.go:33-48`) | `HandlerTriple` needs `rpcCtx`, `decodedAt`, `mdPrin` | recorded out of scope (1.5; 2a "Still open") |
| P14 | grpcproxy `v3rpc.FiltersFromRequest(cr)` (`proxy/grpcproxy/watch.go:272`) | `FiltersFromRequest.spec` (field points-to) | yes |
| P15 | raw-gRPC tests comparing codes and messages (`tests/integration/v3_grpc_test.go:2369-2390`, `eqErrGRPC`) | `ansOutcome` | yes for messages; codes loose (F7, second tier) |

Also: `version.LessThan`/`Cluster` (lessor `greaterOrEqual`, server logs) close: their users only
log the result or decide something the model does not represent. The generic proto specs serve
raft, apply and the client's `Merge`.

## First-tier findings

### F1. Generated stubs and handlers with no spec (3h). RangeStream, Cluster and Maintenance are recorded; the other auth methods are not.

- What the user needs and does not get:
  - Client side: `remoteKVAt_methods.spec` (`client/v3/Api.lean:1039-1051`) includes
    `RangeStreamTriple` of the stub's `RangeStream`. `NewKVClient.spec` promises `remoteKVAt`, so
    its proof needs `kVClient.RangeStream`.
  - `kVClient.RangeStream` is untranslated (absent from `Code/go_etcd_io/etcd/api/v3/etcdserverpb.toml`)
    and has no spec. The client calls it at `retry.go:111-112`.
  - `retryKVClient__RangeStream.lean` "Integration (I1)" cites a stub step that has no spec.
    Its "**Open**: … at `lo = 0`" paragraph is stale: `rangeStreamSpec.up` now carries `lo` and
    `authLb` (`v3rpc/Api.lean:348-352`).
  - The snippet `v3rpc/range-stream` (`examples/specreq/v3rpc/kv.go:117`, `kc.RangeStream`) cannot
    be proved.
  - The same holds for `NewClusterClient`/`NewMaintenanceClient` and their stubs: 1c asked for them
    (`req/go_etcd_io_etcd_api_v3_etcdserverpb.md`, "from 1c" item 2), and
    `RetryClusterClient`/`retryClusterClient__*`/`retryMaintenanceClient__Alarm` cite them. There is
    no spec file for them.
  - Auth: `remoteAuthAt_call.spec` covers every auth request (`ApiClient.lean:790`), but only 6
    `authClient.*` stubs exist (`AuthEnable`, `Authenticate`, `UserAdd`, `UserGrantRole`, `RoleAdd`,
    `RoleGrantPermission`). `UserGet`, `UserList`, `UserDelete`, `UserChangePassword`,
    `UserRevokeRole`, `RoleGet`, `RoleList`, `RoleDelete`, `RoleRevokePermission`, `AuthDisable` and
    `AuthStatus` are untranslated and have no spec. `NewAuthClient.spec` therefore has no proof plan
    for them.
- Server side:
  - `Server.spec`'s post `regsOk B (etcdContract γ ep) …` needs `unaryOk`/`streamOk` of every
    registered generated handler.
  - `kvDesc_init`, `authDesc_init` and `otherDescs_init` (`etcdserverpb/Api.lean:318-366`) leave
    these handlers as opaque existentials: `ss` (`_KV_RangeStream_Handler`), the auth `ms'`
    (11 handlers), and Cluster's and Maintenance's `ms ss`.
  - So no spec gives the step for them. Yet the v3rpc handlers they call are specified
    (`kvServer__RangeStream`, `AuthServer__UserGet`, `ClusterServer__*`, `maintenanceServer__*`).
- Recorded: open-questions 7.4 and batch-3h's "Consolidated translation request" items 1-2 cover
  RangeStream, Cluster and Maintenance.
  - Not recorded: the 11 other Auth stubs and `_Auth_*_Handler`s. Neither list mentions them.
- Fix:
  - Add the 11 auth stubs and handlers to the translation request (7.4).
  - Meanwhile, write each missing stub's spec in WP form, as `kVClient.Put.spec` does
    (`unaryStubWP`/`streamStubWP`), and each handler's as the translated handlers' are. They are
    statements about generated code; they can be stated before translation.
  - In the snippet `v3rpc/range-stream`, cite the stub spec once it exists.

### F2. Kubernetes cannot establish `dialOptsOk` for its dial options (2a)

- Kubernetes' client: `storagebackend/factory/etcd3.go:309-339`.
  - It passes `DialOptions` with `grpc.WithChainUnaryInterceptor` and `WithChainStreamInterceptor`
    (grpc-prometheus), and `grpc.WithStatsHandler(otelgrpc.NewClientHandler(...))`.
  - It also passes `grpc.WithContextDialer` when there is an egress dialer.
- The client's `New` takes `dialOptsOk cfg.DialOptions'` (`client/v3/ApiClient.lean:226-231, 249`).
  That predicate is a slot of 2a's, and its only introduction is `dialOptsOk_nil`.
- 1c asked for the introductions for exactly these options (`req/google_golang_org_grpc.md:160-165`).
  2a has:
  - no spec of `WithChainUnaryInterceptor`, `WithChainStreamInterceptor`, `WithStatsHandler` or
    `WithContextDialer`;
  - no law turning `dialOptAt`s into `dialOptsOk`.
  - `DialCfg.ui`/`si` are a single `Option val`, so it cannot express a chain at all.
- So Kubernetes, the main user of the client, cannot build its client from these specs. No snippet
  covers this pattern: `clientv3client/kubernetes.go` passes no dial options.
- Recorded only as "k8s's non-neutral dial options" under "Still open" in `batch-2a.md:347`. It is
  not a user decision in `open-questions.md`.
- Fix:
  - Model a chain in `DialCfg`: `uis : List val`, the client's interceptor first, then the chained
    ones.
  - Add specs of the four options. `WithStatsHandler` and `WithContextDialer` are `dialOptAt v id`.
    `WithChain*Interceptor` appends interceptors, each taking a premise like `icEtcdOk`'s client
    analogue: it calls its invoker at most once with its own arguments.
  - Add a law `dialOptAt`s ⊢ `dialOptsOk`.
  - Add a snippet with Kubernetes' options.

### F3. `grpc.Peer.spec` mis-types the peer variable; `Peer.String` and `peerOk`'s use have no spec (2a)

- `Grpc.Peer.spec` (`Spec/google_golang_org/grpc/Peer.lean`) takes `p ↦ q ∗ ⌜q = null⌝` with
  `q : Loc`, and `peerVar p`'s invariant holds a `Loc` (`Grpc/Api.lean:801-804`). Both treat `p` as
  a `*peer.Peer` variable.
- In grpc-go, `Peer(p *peer.Peer)` stores `p`, and after the attempt it runs `*o.PeerAddr = *x`, a
  struct copy (`grpc@v1.84.0/rpc_util.go:312-330`).
- The only user declares `var p peer.Peer` (a struct) and passes `&p`
  (`client/v3/retry_interceptor.go:46-47`). It owns `p ↦ (zero peer.Peer)`, so it cannot
  establish the precondition.
- The user then logs `p.String()` (`retry_interceptor.go:71`, `(*Peer).String`,
  `peer/peer.go:46`). That spec existed in the old tree (`grpc/peer/Peer__String.lean`) and was
  dropped.
- On the server side, `peer.FromContext.spec` gives `peerOk p`, which is opaque and has no
  elimination law. So `logUnaryRequestStats`'s `peerInfo.Addr.String()` (`interceptor.go:106`) has
  no source, although its sketch cites "`peer.FromContext` (grpc's)".
- Not recorded.
- Fix:
  - Restate `Peer.spec` over `p ↦ (pv : peer.Peer)`, with the invariant holding a `peer.Peer` value
    whose `String()` returns.
  - Restore `Peer.String.spec`.
  - Add `peerOk_addr`: reading `Addr` gives an interface whose `String()` returns. Or state
    `FromContext` so that it gives exactly that.

### F4. The election and lock services embed registers on the member's server are not in any contract (2a, with 2e)

- After `v3rpc.Server`, embed registers two more services on the same server before serving
  (`server/embed/serve.go:184-186` insecure, `:244-246` secure):
  `v3electionpb.RegisterElectionServer(gs, servElection)` and
  `v3lockpb.RegisterLockServer(gs, servLock)`.
- `Server.spec`'s post (`v3rpc/Server.lean`) is `srvBuild gs B ∗ ∀ ep gq, regsOk B (etcdContract γ
  ep) …`. `regsOk` (`Grpc/Api.lean`) needs `C.unary r.1 = some …` for every registration, and
  `etcdContract` (`v3rpc/Api.lean:392-447`) has no `/v3electionpb.Election/*` or `/v3lockpb.Lock/*`
  entry.
- So after these registrations `regsOk` fails and `Grpc.start` cannot be applied. The other
  possibility is a contract other than `etcdContract`, but then `servesAt_addr` (and
  `grpcOver_inj`) gives no `servesAt`.
- There is no `RegisterElectionServer`/`RegisterLockServer` spec.
- 2e asked for this (`req/go_etcd_io_etcd_server_v3_etcdserver_api_v3rpc.md`, "from 2e" item 3:
  "registered by `v3rpc.Server`"). The request is misattributed: embed registers them, not
  `v3rpc.Server`. It is unanswered.
- `NewElectionServer.lean`'s Users line repeats the misattribution.
- The snippet `v3rpc/serve` registers nothing extra, so no snippet covers this, and every member
  embed starts has these services.
- Not recorded (the in-process `v3client` they run over is, 1.5; the registration is not).
- Fix:
  - Make `etcdContract` constrain only etcd's methods. For example `servesAt γ ep ⊣⊢ ∃ X, addrAt ep
    (etcdContract γ ep ⊕ X)`, with `⊕` taking etcd's table first. Or give `etcdContract` the two
    services' entries with 2e's contracts.
  - Add `RegisterElectionServer.spec`/`RegisterLockServer.spec` (over `Server.RegisterService.spec`
    and the generated descriptors), and a `regsOk` extension law.
  - Add a snippet that registers a second service after `v3rpc.Server`.

### F6. Old specs dropped (coverage hard rule; 2a: a, 3h: b)

PRINCIPLES says "A smaller API is not a narrower scope". These old-tree functions have no spec
here, and their callers still execute them:

- (a) 2a:
  - `grpclog.SetLoggerV2`: Kubernetes' `etcd3` package initializer, `logger.go:27`.
  - `peer.Peer.String`: F3.
  - `HealthCheckResponse_ServingStatus.String`: `v3rpc/health.go:66,75`. The sketch of
    `healthNotifier__startServe.lean` cites "the generated enum stringer".
- (b) 3h:
  - `NewLoggableTxnRequest`: `interceptor.go:163`, and txn's `WarnOfExpensiveReadOnlyTxnRequest`,
    whose sketch cites "3h: a stringer, `stringerOk`".
  - `RangeRequest.String`: `interceptor.go:118`, `v3_server.go:126`.
  - `AlarmType.String`: `apply/backend.go:124,131`.
- `txn/Api.lean:61,492` keeps `stringerOk` "Provisional, 3h's", but no spec introduces it. So every
  `WarnOf*` caller's `stringerOk req` premise has no source.
- Recorded only as "Left out" in `batch-3h.md:142-145` ("untranslated, logging only") and
  `batch-2a.md:178` ("the enum stringers"). Neither is a user decision, and the principle forbids
  dropping these.
- Fix:
  - Restore each as an assumed spec. It returns some string; for the loggable wrappers, a value with
    `stringerOk`.
  - Add a 3h law `stringerOk` of a request message at any fraction.

## Second-tier findings

- **F5 (recorded, 1.5 / batch-2a "Still open").** The in-process `v3client` calls the unary handlers
  directly through the adapters (`v3client.go:33-48`). `HandlerTriple` (`v3rpc/Api.lean:668-675`)
  needs:
  - `rpcCtx ctx md`, which no derived context keeps: there is `ctxInMD_child` but no `rpcCtx_child`;
  - `Proto.decodedAt`, which a client-built message does not have;
  - `etcdUnary`'s `mdPrin`.

  What the handlers need of 2c is only `reqCtxOk`, `reqPrin` and `endsDecoded`. Stating
  `HandlerTriple` over those, with the grpc run as an instance, would serve both callers if the user
  brings the in-process client into scope. Separately, 1c's and 2e's requests for adapter
  introductions (`req/..._etcdserver.md` "from 1c (round 1)" item 1; `req/..._client_v3.md` "from 2e,
  round 1" item 1) are open.
- **F7.** `ansOutcome` (`v3rpc/Api.lean:181-189`) allows `code = Rpctypes.code e ∨ code =
  Grpc.cUnknown` for every error. The Go code sends `Unknown` only for the two `EtcdError` values in
  `toGRPCErrorMap` (`ErrMemberNotEnoughStarted`, `ErrTooManyRequests`); every other mapped error and
  every check error is its `ErrGRPC*` status (`v3rpc/util.go`, `togRPCError`). The raw-gRPC tests'
  `eqErrGRPC` compares codes (`v3_grpc_test.go:2378`). Pin it: `code = if e ∈ {.memberNotEnoughStarted,
  .tooManyRequests} then cUnknown else code e`. The header's "a definite error's code is pinned"
  promises this already.
- **F8 (uncertain; provability).** `version.LessThan.spec` quantifies over any `a b : val`, not
  `semver.Version` values. A non-`Version` value may be stuck in the model, which would make the
  spec false. Take `a b : semver.Version`.
- **Stale or misattributed notes in callers:**
  - `retryKVClient__RangeStream.lean`'s "Open … lo = 0" (F1);
  - `NewElectionServer.lean`'s "Users: v3rpc.Server" (F4);
  - 2e's request item 3 (F4).
- **Recorded, for completeness of the picture:**
  - the TLS+HTTP path's run resource (3.7);
  - `LeaseKeepAlive`'s goroutine outliving its run with a gate share (integration-X open 1);
  - cmux's specs waiting for its translation (`Grpc/Api.lean`, `cmuxSubAt`);
  - the gateway's forwarded watches (`ApiWatch.lean`, 3.8).

## What is good

- The contract design: `etcdUnary`'s three ways and the at-most-once argument through
  `attemptOk_call`.
- The client error path: `rpctypes`' table is exact, and `callErr_*`/`init.spec` serve every
  Kubernetes error check I found.
- The metadata and principal path (`mdPrin_of`/`reqPrin_of_md`) fits the client's and the server's
  sketches.
- The generic proto specs replace an 18-file per-type family without losing a user.
- The watch server's scope restrictions are honest and recorded.
- Every Lean name another area cites resolves.
