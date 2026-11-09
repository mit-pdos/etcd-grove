# Verification round: A2 (client watch, lease, lifecycle), completeness

Reviewer: completeness kind, independent. Worktree `specs-only` at `1aa6fc1337`. Sources: `.lake/src/*`
(the pinned fork `a4d2bb17`), Kubernetes `k8s.io/apiserver@v0.0.0-20261021221356-9c4ec15b8038`,
`examples/`. I wrote the findings below before I read `batch-1b.md`, `batch-1c.md`,
`open-questions.md` and `integration-*.md`. I read them afterwards only to mark findings that are
already recorded.

## Verdicts

| batch | verdict |
|---|---|
| **1b** (watch: `ApiWatch.lean`, `watcher__*`, `watchGRPCStream__*`, `Client__Watch`, `Client__RequestProgress`, snippets `clientv3watch/`) | **PASS WITH OPEN DECISIONS**: 1.1 (watch responses are facts, liveness unstated), 1.2 (a refused watch delivers nothing only on an up-to-date member), 1.5 (in-process watches out of scope), A17 (`exactFrom` gate) |
| **1c** (lease, lifecycle, auth, cluster, maintenance, interceptors, `kubernetes/`, `credentials/`, `internal/`, `client/pkg/v3/`, snippets `clientv3lease/`, `clientv3client/`) | **FAIL** (F1-F4) |

## First-tier findings (all 1c)

### F1. `kubernetes.New` drops the endpoints token, so no Kubernetes client can call `Status`

- **File**: `Spec/go_etcd_io/etcd/client/v3/kubernetes/New.lean:39-50`. Its post is
  `kc ↦ {…} ∗ clientMut c γ who` or an error. `clientv3.New`'s post (`New.lean:57-63`) also gives
  `⌜AutoSyncInterval ≠ 0⌝ ∨ ∃ eps, cfg.Endpoints' ↦*□ eps ∗ epsTok c (DFrac.own 1) eps`, and the
  "no endpoint ⇒ error" fact. `kubernetes.New` is `clientv3.New(cfg)` plus a wrapper
  (`client/kubernetes/client.go:28-38`), and its sketch says "as `clientv3.New`'s", with Margin
  "none". Nothing else produces `epsTok`: the only sources are `New`'s post and `epsTok_persist`.
- **Step that does not close**: `Maint.StatusTriple` (`ApiClient.lean`, the `Status` triple) needs
  `epsTok c dq eps ∗ ⌜eps ≠ []⌝` for a client that dials (`maintOf v c`, `c ≠ null`). So do
  `Client.Dial`, `checkVersion`, `SetEndpoints`, `Sync` and the per-member `clientVia`.
- **Users not served**:
  - Kubernetes' feature checker (`storage/feature/feature_support_checker.go:142,194`), which
    `etcd3/store.go:243` runs on every store. This package is translated
    (`Code/k8s_io/apiserver/pkg/storage/feature.toml`).
  - The storage health check (`storagebackend/factory/etcd3.go:277`).

  The snippets `ReqEndpoints` and `ReqStatus` take a `*clientv3.Client` from `clientv3.New`, so they
  do not cover the `kubernetes.New` path.
- **Fix**: copy `clientv3.New`'s two extra conjuncts into `kubernetes.New`'s post, the token at
  `kc.Client`'s `c`. Add a snippet `ReqKubeStatus`: `kubernetes.New`, then `Endpoints`, then `Status`
  of each endpoint.

### F2. `dialOptsOk` can only be introduced for `nil` options, so Kubernetes' client cannot be built

- **File**: `ApiClient.lean`, `dialOptsOk`. Its only introduction is `dialOptsOk_nil.spec`. A
  repository-wide grep finds no other law, and no relation to grpc's `dialOptAt`.
- **The spec's own claim**: `New.lean` "Changes" says it admits "Kubernetes' dial options". The
  `dialOptsOk` doc names "chained interceptors, stats handlers, context dialers" and the proxy's
  `WithUnaryInterceptor`. No caller can produce `cfgOk` for any of these.
- **Users not served**:
  - Kubernetes' `newETCD3Client` (`storagebackend/factory/etcd3.go:308-327`, then
    `kubernetes.New` at `:352`) passes `grpc.WithChainUnaryInterceptor`,
    `WithChainStreamInterceptor`, `WithStatsHandler` and `WithContextDialer`.
  - The gRPC proxy's client (`etcdmain/grpc_proxy.go:344-349`) passes `WithUnaryInterceptor` and
    `WithStreamInterceptor`.
  - Grpc has specs only for `WithUnaryInterceptor`, `WithStreamInterceptor`, `WithKeepaliveParams`,
    `WithResolvers`, `WithTransportCredentials` and `WithPerRPCCredentials`. It has none for the
    `WithChain*` dial options, `WithStatsHandler` or `WithContextDialer`. The
    `ChainUnaryInterceptor.lean` and `StatsHandler.lean` that do exist are server options.

  The snippets `ReqKubeNew` and `ReqNewTLS` pass no `DialOptions`, so they do not rely on this.
- **Already requested, not delivered**: `req/google_golang_org_grpc.md:160-165` (Kubernetes'
  options) and `:260` (the proxy's). It is not listed in `open-questions.md`.
- **Fix**:
  - Add a law `dialOptsOk_of : sl ↦*□ vs ∗ [∗list] v ∈ vs, (∃ f, dialOptAt v f ∗ ⌜f keeps the
    client's credentials and calls each invoker at most once⌝) ⊢ dialOptsOk sl`, or one law per kind.
  - Add 2a's specs of the four missing grpc dial options.
  - Make `ReqNewTLS` pass Kubernetes' four options.

### F3. `NewKVFromKVClient` cannot be called on an in-process client, so `ReqInProcClient` is unprovable

- **File**: `Spec/go_etcd_io/etcd/client/v3/NewKVFromKVClient.lean:39`. The pre is
  `⌜c = null⌝ ∨ ∃ γ' who', clientConnOk c γ' who'`.
- **Step that does not close**: `NewCtxClient.spec` gives `clientBare c none`. The only law out of
  it, `clientBare_base`, gives `clientBase`, not `clientConnOk`. Its sibling constructors take
  `⌜c = null⌝ ∨ clientBase c who`: `NewLeaseFromLeaseClient`, `NewAuthFromAuthClient`,
  `NewClusterFromClusterClient`, `NewMaintenanceFromMaintenanceClient` and `NewWatchFromWatchClient`.
  The code reads only `c.callOpts` (`client/kv.go:151-157`), as the siblings do. The snippet
  `examples/specreq/clientv3client/inproc.go` (`ReqInProcClient`: `c.KV =
  clientv3.NewKVFromKVClient(kvc, c)` on `NewCtxClient`'s `c`) therefore cannot meet the pre.
- **Users not served**:
  - `v3client.New` (`server/etcdserver/api/v3client/v3client.go:34`), the in-process client of
    v3lock and v3election.
  - The file's own Users list omits it.
- **Related open item**: open question 1.5 (the in-process client: watches out of scope;
  "`isClient_conn` is false for an in-process client"). The snippet nevertheless asserts that the
  KV half works.
- **Fix**: take `⌜c = null⌝ ∨ clientBase c who'` as the siblings do. This also needs `clientBase`'s
  realization to list `callOpts` (`callOptsOk _ false`), as `integration-I1.md` item (2) already
  asks.

### F4. Coverage: `(*types.ID).String` lost its spec, and server sketches cite the value form at pointer calls

- **The old spec**: `specs-ref/Spec/go_etcd_io/etcd/client/pkg/v3/types/ID__String_ptr.lean`. It
  exists because `types` is translated names-only, so the pointer wrapper is not related to
  `ID.String`. It has no counterpart here; this is the only missing file of the area against
  `specs-ref`.
- **The pointer calls in translated code**: 144 calls of `MethodResolve (PointerType types.ID.ty)
  "String"`, in `etcdserver.lean`, `api/rafthttp.lean` and `api/membership.lean`. Examples:
  `streamWriter.run` (18 calls), `streamHandler.ServeHTTP` (17), `RaftCluster.RemoveMember` (9),
  `checkClusterCompatibilityFromHeader` (5).
- **Sketches that misuse the value form**: `rafthttp/checkClusterCompatibilityFromHeader.lean:6`
  and `rafthttp/streamReader__dial.lean:6` cite "`ID.String` (1c)". That is the value-receiver
  triple (`types/ID__String.lean:37`), which does not apply to those calls.
- **Fix**: restore `ID.String_ptr.spec` in `Spec/go_etcd_io/etcd/client/pkg/v3/types/`, at any
  fraction with the points-to kept. Point the rafthttp, membership and etcdserver sketches to it.

## Second-tier findings

- **S1. No `ctxPrin` introduction for a server-side context.** The in-process client forwards a
  token as *incoming* metadata (v3lock/v3election → `v3client` → adapter → `AuthInfoFromCtx`, which
  reads `metadata.FromIncomingContext`, `server/auth/store.go:1077`). All of `ctxPrin`'s
  introductions are about *outgoing* metadata:
  - `ctxPrin_of_noMeta` (via `ctxNoMeta`: no `mdOutgoingKey`);
  - `ctxPrin_token` (via `ctxTokenMd`: outgoing `token`).

  Two consequences:
  - `Api.lean`'s `ctxPrin` doc says `ctxPrin_token` covers "the in-process `v3client`"; it does not.
  - `ctxPrin_of_noMeta` at `dflt = none` gives `ctxPrin none ctx none` for such a context. An
    in-process client would be authenticated as the token's user, so the law is true only if
    in-process clients are outside `ctxPrin`'s meaning.

  `lockServer.Lock.spec` takes `isClient c γ dflt ∗ ctxPrin dflt ctx who` as premises, and its
  untranslated caller has nothing to discharge them with. This falls under A5 and 1.5 (recorded);
  the wrong doc sentence is not recorded.
- **S2. `Client.ActiveConnection` has a user and nothing to serve it.** Its spec says "no user in
  scope", but Kubernetes' `blockUntilReady` (`factory/etcd3.go:358-380`) calls it. That caller then
  calls `GetState`, `Connect` and `WaitForStateChange`, and `connOk` gives no specs for them.
  Recorded as not done (C-S1, `batch-1c.md:164`). Fix: correct the Users line.
- **S3. Promoted methods of `*kubernetes.Client` have no specs.** The translated Kubernetes code calls
  `Ctx` (`etcd3/store.go:243`) and `RequestProgress` (`store.go:108`) on `*kubernetes.Client`
  (`MethodResolve (PointerType kubernetes.Client.ty)`). The feature checker reaches `Endpoints` and
  `Status` through its own interface on the same dynamic type. PRINCIPLES ("canonical specs are per
  (concrete type, method)") asks for one spec per such pair, each a one-line corollary of the
  `*clientv3.Client` spec. The old tree had none either.
- **S4. Pointer forms of `types.URLs` methods have no specs.** `(*URLs).StringSlice` is called by
  `NewServer`, and `(*URLs).Len` by rafthttp's `setPeerURLsHeader`. Only the value forms have specs
  (`URLs__StringSlice.lean`). This is the same root cause as F4, and the old tree lacked them too.
- **S5. Kubernetes' watch context.** `Watcher.WatchTriple` takes `Context.ctxOk ctx`. Kubernetes
  passes a request context wrapped by `WithRequireLeader` (`store.go:1154-1162`). Fine within the
  recorded K4 decision ("A context outside Perennial's model"), noted only for completeness.
- **S6. The gRPC proxy's coalescing gets a weaker floor than it uses.** The proxy sets
  `nextrev = Created.Header.Revision + 1` (`grpcproxy/watch_broadcast.go:83-85`) and relies on
  every event above `H` being delivered. The spec gives that only above `r0 ≥ H` (`WatchPos.init 0
  r0`), which leaves `(H, r0]` uncovered. It is a known margin (`issues/etcd-watch-current-resume-past-event.md`;
  `batch-1b.md` withdrew its grpcproxy lead), and the proxy is untranslated.
- **S7 (uncertain).** `nonissues/etcd-client-dialoptions-unary-interceptor.md` says a caller's
  `WithUnaryInterceptor` replaces the client's. At the pinned fork, `dialSetupOpts` appends the
  caller's `dopts` *before* the client's interceptors (`client/client.go:239` vs `:266-271`). Grpc
  keeps the last `WithUnaryInterceptor`, which would be the client's. The `dialOptsOk` doc
  ("`WithUnaryInterceptor` … which replace the client's") may therefore describe an older ordering.
  I did not run the nonissue's test at the pin.

## What is good

- **Watch.** The `watchStep` facts serve every watch pattern I found:
  - gap-free resume after a `Get` (`ReqWatchFromGet`, used by `naming`, `mirror`, `v3discovery`,
    `leasing.monitorLease`, Kubernetes `watcher.go:493`, the cache's `cache.go:392`);
  - wait-for-delete (`concurrency/key.go:30`, `leasing/kv.go:210`, `recipes/watch.go:28,38`);
  - whole revisions, order and progress bookmarks (the cache's `validateRevisions`/`demux`,
    Kubernetes);
  - the error response with no events, which `Election.observe`'s unchecked loop (`election.go:223`)
    relies on;
  - `PrevKv` nil-or-correct (Kubernetes `event.go:67`);
  - `Created` first (grpcproxy, the cache);
  - keys within the range (namespace's `Key[len(pfx):]`);
  - sharing a response read-only (cache, `observe`).

  `watchRespAt` gives the header owned in full on event responses, which is what `observe`'s
  `hdr.Revision = …` needs. The fork's `Header: &pb.ResponseHeader{}` on `closeErr` responses
  (`watch.go:366,381,500`) makes `wr.Header.Revision` safe for every reader. The 18 watch snippets
  cover every pattern above with an explicit panic.
- **Callers' sketches fit the watch specs.** Checked: `Concurrency.waitDelete`, `Election.observe`,
  `leasingKV.monitorLease`, `recipes.WaitEvents`/`waitEvents` (`p.done = some (rev-1)` from both of
  `Watch`'s outcomes), `Cache.watchEvents` (`watchChAt_recvAu`, `watchRespAt_persist`, monotonicity
  of `exactFrom`), and 2a/2b's use of `watchSpec`, `wsReq` and `wsSt`. The names exist; the premises
  are available from `isClient_fields`/`clientRest_fields` and the context laws; the posts suffice.
- **Lease.**
  - `Session` (`session.go:41-115`): a persistent grant update, `kaChan` drained in a `for range`,
    `Revoke` that may answer `ErrLeaseNotFound` after a resend.
  - Kubernetes' lease manager (`lease_manager.go:109`): the id and TTL.
  - The examples' per-member `Leases`/`TimeToLive` (`via`, `leaseViewLb`).
  - `KeepAliveOnce`'s three outcomes, which match `lease.go`.

  `NewSession.spec` and `lockServer.Lock.spec` use `Lease.GrantTriple`/`KeepAliveTriple` correctly.
- **Lifecycle, auth, cluster, maintenance.** For `clientv3.New` clients:
  - New/close, wrapping `KV`, `Ctx`, `Endpoints`/`Status`;
  - the admin set-up, user-client, refused-principal and token-refresh patterns
    (`examples/etcd/auth`);
  - `MemberAdd`/`MemberList` with `urlsRight`;
  - alarm disarm and `Sync`.

  These are covered and the pres can be established from what the callers hold.
- **Coverage.** Every spec file of the area in `specs-ref` has a counterpart here except
  `ID__String_ptr` (F4).

## Counts

- **Specs checked against users**:
  - the three vocabularies (`ApiWatch`, `ApiLease`, `ApiClient`) and W0's client slots they fill;
  - about 60 user-facing specs (the `watcher`/`Client` watch triples, the `lessor`/`Client` lease
    triples, `New`, `NewCtxClient`, the `From*Client` constructors, `kubernetes.New`, `Close`,
    `Ctx`, `Endpoints`, `Status`, `ActiveConnection`, the auth, cluster and maintenance bundles);
  - coverage of all 347 + 34 files against `specs-ref`.

  4 do not close: `kubernetes.New`, `cfgOk`/`dialOptsOk`, `NewKVFromKVClient`, and the missing
  `ID.String_ptr`.
- **Snippets checked**: 46 (18 watch, 9 lease, 19 client). 45 close; `ReqInProcClient` does not
  (F3). `ReqNewTLS` and `ReqKubeNew` close but omit the dial options, so they miss F2's pattern.
- **Users checked**: about 40 call sites (22 watch, 6 lease, 12 lifecycle/maintenance) in 22
  patterns. 19 are served. Not served:
  - Kubernetes `Status` on a `kubernetes.New` client (F1);
  - Kubernetes' and the proxy's dial options (F2);
  - the in-process client's KV (F3).

  Partially served: S1-S3.
- **Callers' specs checked**: 9 (`waitDelete`, `Election.observe`, `monitorLease`, `WaitEvents`,
  `waitEvents`, `Cache.watchEvents`, `NewSession`, `lockServer.Lock`,
  `checkClusterCompatibilityFromHeader`). 8 fit; `checkClusterCompatibilityFromHeader` does not (F4).

No new bug in the Go code. The fork already fixed the one candidate (a nil `Header` on `closeErr`
responses, which the gRPC proxy would dereference).
