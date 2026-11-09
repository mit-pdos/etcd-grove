# Batch 1c, completeness review, round 1

Reviewer: completeness. Batch 1c covers the client's lease, lifecycle, auth, cluster and maintenance
APIs, the interceptors, `client/v3/kubernetes`, `credentials`, `internal/*` and `client/pkg/v3/*`.
This round reviews the working tree on `specs-only` at `581b58e9e5` plus uncommitted edits. Sources
read:

- the vocabularies: `Spec/go_etcd_io/etcd/client/v3/{ApiClient,ApiLease}.lean`, `kubernetes/Api.lean`,
  `client/pkg/v3/transport/Api.lean`;
- the specs of `New`, the `lessor` methods, `Client.{Close,Ctx,Endpoints,Sync,ActiveConnection}`,
  the `From*Client` constructors, `kubernetes.New` and `CreateDefaultZapLogger`;
- W0's `Api.lean` (`isClient`, `clientRest`, `ctxPrin`) and `Model.lean`
  (`leaseStep`, `clusterStep`, `authStep`, `Step`);
- the snippets `examples/specreq/{clientv3lease,clientv3client}/`, which pass `go vet`;
- the batch's `req/` sections. I read `notes/specs-only/batch-1c.md` only after forming the findings
  below.

Users scanned:

- the pinned etcd client (`concurrency`, `leasing`, `experimental/recipes`) and its server
  (`etcdmain/grpc_proxy.go`, `proxy/grpcproxy/*`, `etcdserver/api/{v3client,v3lock,v3election}`);
- the Kubernetes apiserver at `k8s.io/apiserver@v0.0.0-20261021221356-9c4ec15b8038`
  (`storage/etcd3/{lease_manager,store,compact}.go`, `storagebackend/factory/etcd3.go`,
  `storage/feature/feature_support_checker.go`);
- this repository's `examples/` (`etcd/{lease,leasegrant,leaseexpiry,leasecatchup,auth,...}`,
  `k8s/*`, `lib/{etcdstart,cluster3}`).

The cache does not use the 1c API, apart from the client fields W0 covers.

## The usage patterns

In the snippet column, "--" means no snippet covers the pattern, and F*n* and S*n* point to the findings below.

| # | Pattern (what the user relies on) | Example call site | Snippet | Pre establishable / post sufficient |
|---|---|---|---|---|
| L1 | `Grant`: the returned id becomes the caller's lease, with TTL at least the one asked. Duplicate grants are harmless. | `concurrency/session.go:50`; k8s `lease_manager.go:109` | `ReqGrantTTL` | yes / yes. `leaseGrantReply` gives the id and TTL, and `leaseStep` gives `id' ≠ 0`, `ttl ≤ ttl'`. |
| L2 | A put, or Kubernetes' `OptimisticPut` with `LeaseID`, on a granted lease, possibly a reused lease id: the put either applies with the lease or fails with `ErrLeaseNotFound`. | k8s `store.go:378`; `concurrency/mutex.go` | `ReqGrantThenPut` | yes / yes |
| L3 | `KeepAlive` drained until the channel closes. Called with a `WithCancel` child, with an incoming server context (v3lock), or in loops (grpcproxy, v3election). Takes no token. | `session.go:58`; `grpcproxy/lease.go:279`; `v3lock/lock.go:35` | `ReqSessionLifecycle`, `ReqKeepAliveValues` | yes for the client's own contexts. The server context is W0's open question 7. |
| L4 | A keep-alive response's `ID` and `TTL` (positive), its header forwarded read-only | `grpcproxy/lease.go:322-330` | `ReqKeepAliveValues` | yes / yes |
| L5 | `Revoke`: success or `ErrLeaseNotFound`, error returned as is | `session.go:112`; `grpcproxy/lease.go:90` | `ReqSessionLifecycle` | yes / yes. No user distinguishes `ErrLeaseNotFound`. |
| L6 | `TimeToLive`: the answer is about the lease asked for, with keys; not found reads as `TTL -1` | `examples/etcd/lease/leasekv.go:77-83`; `grpcproxy/lease.go:104`; `leaseexpiry.go:79-85` | `ReqTimeToLiveAbout` | yes / yes, as far as panics go |
| L7 | `Leases` lists no id twice | `leasekv.go:63-73` | `ReqLeasesNoDup` | yes / yes |
| **L8** | `Leases` on one member lists a lease granted through it, never one that member found gone, and, once caught up, everything granted before | `examples/etcd/leasegrant/leasegrant.go:61-80`; `leaseexpiry.go:69-102`; `leasecatchup.go` | -- | **no / no** (F1) |
| C1 | `New` with plain endpoints, timeouts, keepalive and a logger | `examples/lib/etcdstart/common.go:215` | `ReqNewWrapClose` | yes |
| C2 | `New` with user name and password | `examples/etcd/auth/authkv.go:123` | `ReqUserClient` | yes (`cfgPrincipal_user`) |
| C3 | `kubernetes.New` with `MaxUnaryRetries: 1`, then the KV field wrapped | `examples/k8s/etcd3/k8setcd3.go:1091` | `ReqKubeNew` | yes |
| **C4** | Kubernetes' real construction: TLS from `transport.TLSInfo.ClientConfig()`, chained interceptors, stats handler, context dialer, a `Named` logger | k8s `factory/etcd3.go:292-349` | -- | **no** (F5) |
| **C5** | The gRPC proxy's client: `DialOptions` with `WithUnaryInterceptor`/`WithStreamInterceptor`, a per-call principal | `etcdmain/grpc_proxy.go:344-349` | -- | **no** (F4) |
| **C6** | The in-process client (`NewCtxClient`, `WithZapLogger`, the `New*From*Client` constructors), which v3lock and v3election use | `etcdserver/api/v3client/v3client.go:29-50`; `embed/serve.go:148` | -- | **no** (F3) |
| C7 | `Close` (teardown, possibly twice, concurrently) | k8s `factory/etcd3.go:252,449,485,496` | `ReqNewWrapClose` | yes for `isClient` holders. Not for `clientRest` holders (S5). |
| **C8** | `Ctx()` (and `GetLogger`) of a client whose `KV` field was replaced (`clientRest`) | `leasing/kv.go:57` via `grpc_proxy.go:488-497`; `leasing/NewKV.lean`'s sketch | `ReqCtxPut` (only for `isClient`) | **no** (F2) |
| C9 | `Endpoints()` as a fresh list, iterated, then `Status` of each | k8s `compact.go:58-71`; `feature_support_checker.go:142` | `ReqEndpoints` | yes |
| **C10** | `Status(ctx, ep)` **promoted on `*Client`**, reading `DbSize` and `Version` | k8s `factory/etcd3.go:277`; `feature_support_checker.go:194` | `ReqStatus` (through the `Maintenance` field only) | **no spec for `(*Client).Status`** (F6) |
| C11 | `ActiveConnection()`: raw stubs (with `grpc.WaitForReady(true)`); `GetState`, `Connect`, `WaitForStateChange` | `grpcproxy/{lease,cluster,auth,maintenance}.go`; k8s `factory/etcd3.go:362-380` | -- | partly (S1) |
| A1 | An administrator's setup with auth off | `authkv.go:298-322` | `ReqAdminSetUp` | yes |
| A2 | A user client's writes count as that user's; a token refresh at most once | `authkv.go:123`, workloads | `ReqUserClient`, `ReqRefreshAtMostOnce` | yes |
| **A3** | With auth on, an anonymous client's or a foreign-token context's request is refused (`refused`) | `authkv.go:151-164`, `Work` | -- | **no** (F7) |
| M1 | `MemberAdd`, then `MemberList` | client's `Sync`; grpcproxy (raw stubs) | `ReqMemberAddThenList`, `ReqSync` | yes |
| M2 | `AlarmDisarm` / `AlarmList` | (etcdctl, e2e) | `ReqAlarmDisarm` | yes |
| K1 | Kubernetes `Get`, `List`, `OptimisticPut` (CAS) | k8s `store.go:299,607,1084` | `ReqKubeCAS`, `ReqKubeList` | yes |
| K2 | Kubernetes `OptimisticDelete` with `GetOnFailure`, and `Count` | k8s `store.go:469,667` | -- | yes by the specs' shape; no snippet (S3) |

### Does any user rely on `LeaseGrant` being applied at most once?

No in-scope user does. The design question raised by the spec's repeatable `Grant` and `Revoke` is
therefore settled in its favour.

- **`concurrency.Session`** (`session.go:50`) keeps `resp.ID`, the last firing's id. An extra lease
  is never kept alive and expires. Mutex keys are named after the session's lease, and they stay
  distinct among live leases because each firing needs `σ.leases id' = none`. 1d's review
  (`reviews/1d-provability-1.md`, "Retried mutable RPCs") reaches the same conclusion.
- **Kubernetes' lease manager** (`lease_manager.go:109-119`) caches one id and reuses it on the local
  clock. A duplicate lease is leaked and expires. Nothing counts leases. The examples' k8s store uses
  no TTL (`k8setcd3.go`).
- **`examples/etcd/{leasegrant,leaseexpiry,leasecatchup}`** check listings against the id the call
  returned. Extra firings add leases a listing may show, which none of these checks forbids.
  `leasecatchup` grants a bounded number of fillers but bounds nothing by the number of leases.
- **Revoke**: no user branches on `ErrLeaseNotFound` (searched across client, server, proxy, cache
  and k8s).
- **The old spec was persistent too.** `lessor.Grant` at `037bf21c75` took `□ ▷ Spec (ttl, 0) Q`.
  The Changes section of `lessor__Grant.lean` ("an exclusive update") misstates it (S4).

A late firing after `Grant` returns is possible, because an attempt that hit a per-attempt timeout
may still be in flight. Its only consequence is another leaked lease. The model lets an expired id
be granted again, so a late `Revoke` could revoke a re-granted lease. That is a model question for
W0 (ids are never reused in practice), not a 1c reliance.

## First tier

### F1. The per-member lease reads of three verified examples are not served (`lessor.Leases`, `lessor.TimeToLive`)

Three examples are closed theorems at `037bf21c75`:

- `examples/etcd/leasegrant` (`leasegrant_Main`: "a panic unless the listing has the lease granted");
- `examples/etcd/leaseexpiry` (`leaseexpiry.go:93-102`: "Leases listed the lease after TimeToLive
  found it gone");
- `examples/etcd/leasecatchup` (member 3, once caught up, lists the first lease).

Their Go code relies on L8. The new chain cannot prove any of them:

- `leaseStep .leaseLeases` (Model.lean:961-963) admits any duplicate-free list of granted ids.
- `.leaseTimeToLive` admits `.err .leaseNotFound` at any state.

The server's `LeaseLeases` (`v3_server.go:737-749`) reads only the answering member's lessor, so no
cluster-level statement is true. A per-member view is needed. W0 records this as open question 6
(C-F6). 1c has no snippet for the pattern, does not list it among its own open questions, and its
`lessor__Leases.lean` Users line claims "a granted id listed" and a snippet `ReqLeasesGranted` that
does not exist.

This breaks "a smaller API is not a narrower scope": these are verified results.

**Fix (1c's part):**

1. Add the three reliance snippets to `clientv3lease/reads.go`: grant, then `Leases` through the same
   one-member client lists it; not found, then never listed; caught up, then listed. Mark each
   `Assumes: W0 open question 6 (per-member lease views)`.
2. Cite the open question in `batch-1c.md`'s open questions.
3. Correct the Users line.

**Once W0 decides:** `Leases` and `TimeToLive` would take the answering member's lower bound
(something like `lessorLb γ ep ls`, persistent, monotone). A client of one endpoint carries it
from `Grant`'s post to `Leases`' post (`ids ⊇ ls`). This is the "per-member views with a monotone
lower bound" option W0 lists, and it serves all three examples.

### F2. A client whose `KV` field was replaced cannot call `Ctx()`, `GetLogger()`, `Endpoints()` or `Close()`

W0's round-2 `clientRest` (`Api.lean:958-965`) has only `isClient_rest`, `clientRest_conn` (to
`clientConnOk`) and `clientRest_fields`. 1c's `Client.Ctx.spec`, `Client.Endpoints.spec` and
`Client.GetLogger` take `clientPre`, and `Client.Close.spec` takes `isClient`. No law leads from
`clientRest`, or from `clientConnOk`, to `clientPre`: `clientConnOk_core` goes the other way.

Who relies on it:

- `leasing/NewKV.lean`'s sketch, lines 11 and 18: "`cl.Ctx()` (1c, over `clientRest`)" and
  `NewSession` over `clientRest`;
- the gRPC proxy, which calls `client.Ctx()` at `grpc_proxy.go:492,497` after line 488 replaced
  `client.KV`;
- `leasing/kv.go:57`, `cctx, cancel := context.WithCancel(cl.Ctx())`.

So the reason `clientRest` exists (1e's item 1) is not delivered.

**Fix:** a law `clientRest_pre.spec : clientRest c γ who ⊢ clientPre c γ who` (or `⊢ clientCore`).
1c realizes `clientRest`, so it can prove this; `clientCore` holds nothing of the `KV` field. Then
`Client.Close.spec` over `clientRest` (S5).

### F3. The in-process client (`v3client.New`) has no spec path, so v3lock and v3election are not served

`v3client.New` (`server/v3/etcdserver/api/v3client/v3client.go:29-50`) builds the client v3lock and
v3election use (`embed/serve.go:148`; `v3lock/lock.go:35-46` calls `concurrency.NewSession(ls.c, ...)`,
`ls.c.Delete`). It does so with:

- `clientv3.NewCtxClient(ctx, clientv3.WithZapLogger(lg))`;
- each field set by `NewKVFromKVClient`, `NewLeaseFromLeaseClient(lc, c, time.Second)`,
  `NewWatchFromWatchClient`, `NewMaintenanceFromMaintenanceClient`, `NewClusterFromClusterClient`
  and `NewAuthFromAuthClient`, each over an adapter.

What is missing:

- `batch-1c.md` "Left out" lists `NewCtxClient` and `WithZapLogger` as "no user in scope". The brief
  names these users.
- No spec gives `clientCore`, `clientPre` or `clientRest` for a `NewCtxClient` client. The
  `From*Client` specs require `clientCore c γ who` (`NewLeaseFromLeaseClient.lean`).
- No law assembles `isClient` from fields set by hand.

The principal question is real here. The adapters pass the caller's context straight to the
server, so a v3lock RPC is authenticated as the gRPC caller (its incoming metadata), not as a fixed
`who`.

**Fix:**

- `NewCtxClient.spec` giving a writable client under construction. Its `ctx` is a `WithCancel`
  child (`ctxOk`; `ctxPrin` from the argument's), its logger `isLogger` (`WithZapLogger`'s, or
  `NewNop`), and no connection.
- A law `clientUnderConstruction ∗ (each field ↦ v with its bundle) ⊢ |==> isClient c γ who`
  (or `clientRest`).
- `remote*At` introductions for the adapters, requested from the server batch.

Put the per-call principal to the user as a decision: a `who` fixed by the contexts the in-process
server's handlers pass, `ctxPrin ctx who` per call. Also file `NewLeaseFromLeaseClient(remote, nil, t)`
(below) since `v3client` always passes a client.

### F4. The gRPC proxy's own client cannot meet `cfgOk`

`etcdmain/grpc_proxy.go:344-349` appends `grpc.WithUnaryInterceptor(grpcproxy.AuthUnaryClientInterceptor)`
and `grpc.WithStreamInterceptor(...)` to `cfg.DialOptions`. `dialOptsOk` excludes them (its
docstring, `ApiClient.lean`). The effect is the one in `nonissues/etcd-client-dialoptions-unary-interceptor.md`:
the client's retry interceptor is replaced. The proxy's interceptor (`grpcproxy/util.go:59-75`)
forwards each call's incoming token, so the principal is per call.

The brief names grpcproxy as a user; `New` cannot be called at its one in-tree construction site.

**Fix:** either (a) record the proxy's client as out of scope, an open question with this call site,
or (b) admit a configuration with no retry interceptor. `uiOk` becomes "one attempt per call", which
`AttemptTriple` already gives, and the per-call principal is shared with F3. Also add
`grpc_proxy.go:344` to the nonissue as an in-tree user: it is no longer only a documentation concern.

### F5. Kubernetes' real client construction has no source for `tlsCfgOk` or `tlsPrincipal` (the batch's own `client/pkg/v3/transport`)

`factory/etcd3.go:286-299` builds `tlsConfig` with `transport.TLSInfo{...}.ClientConfig()`. That
function is in this batch's package, translated names-only (`Code/.../transport.toml`), and has no
spec (`Spec/.../transport/` holds only `IsClosedConnError`). `cfgOk`'s `(TLS = null ∨ tlsCfgOk TLS)`
and `cfgPrincipal_tls` (`tlsPrincipal`) therefore have no producer at the production call site. No
snippet uses TLS.

The same construction needs two more producers, already requested from other batches (no new 1c
work): zap's `Logger.Named` (`etcd3.go:94`; W0's C-S5, not done) and `dialOptsOk` introductions for
the chained interceptors, stats handler and context dialer (requested from 2a in
`req/google_golang_org_grpc.md` item 2).

**Fix:**

- a trust-boundary `TLSInfo.ClientConfig.spec` returning `tlsCfgOk cfg` or an error. The empty
  `TLSInfo` case (which Kubernetes discards, `etcd3.go:297-299`) gives a non-nil config.
- the request for `tlsPrincipal`'s introduction to the server batch (2e) restated with this producer.
- a snippet `ReqNewTLS` (`clientv3client/lifecycle.go`) in Kubernetes' shape: `ClientConfig`, `nil`
  when no files are given, `kubernetes.New`.

### F6. No specs for the promoted non-KV methods of `*Client`; Kubernetes calls `Status` on the client

Kubernetes calls `t.client.Status(ctx, ep)` (`factory/etcd3.go:277`, where `client` is
`*clientv3.Client`) and `c.Status(ctx, endpoint)` (`feature_support_checker.go:194`, through an
interface whose dynamic type is `*clientv3.Client`). That is `Maintenance.Status` promoted through
`Client`'s embedded field. The batch has no `Client__Status.lean`, so the caller has no spec to apply.

W0 added `Client.{Get,Put,...}` for exactly this reason ("so that their proofs need no dispatch
lemma", `Client__Get.lean`). PRINCIPLES' canonical-spec rule includes promoted methods. The snippets
dodge the issue by calling through the fields (`cli.Maintenance.Status`).

**Fix:** `Client__Status.lean`, by `isClient_fields`' `maintAt` and `maintAt_methods`, as
`Client__Get` does. The same mechanical file is needed for the other promoted `Lease`, `Auth`,
`Cluster` and `Maintenance` methods users call on the client: `cli.MemberList` in the examples'
tests, and etcdctl. Add the `Status` one to `ReqStatus`.

### F7. The auth example's refused principals are not covered, and one is not establishable

`examples/etcd/auth/authkv.go:151-164` runs two principals that must be refused (`refused` panics if
`err == nil`):

- `anon`: the client with no credentials, so `cfgPrincipal_none`;
- `bad`: the same client, with `metadata.AppendToOutgoingContext(ctx, "token", badToken)`.

That example is a verified result at `037bf21c75`.

- **anon:** the spec chain looks sufficient. `Step none` with auth on gives a refusal, and the
  interceptor returns `ErrUserEmpty` unrefreshed (`shouldRefreshToken` with a nil bundle,
  `retry_interceptor.go:163-166`).
- **bad:** the request needs `ctxPrin ctx none` for a context carrying a token that names no user.
  `ctxPrin`'s introductions (W0, `Api.lean:525-533`) cover only metadata-free contexts and say "a
  context a caller builds with grpc metadata of its own needs an introduction from grpc's metadata
  (2a)". No such introduction is requested. The interceptor's path for `ErrInvalidAuthToken` with
  no bundle is 1c's own: `refreshToken` returns `nil`, and the request is resent until `max`, then
  the refusal is returned (`retry_interceptor.go:95-105,173-178`). `uiOk_call` must allow it.

Neither pattern has a snippet in `clientv3client/auth.go`.

**Fix:**

- a snippet `ReqRefusedPrincipals`: anonymous and foreign-token puts with auth on, panicking if
  either succeeds;
- a request (to W0, and to 2a for `metadata`) for an introduction
  `metadata.AppendToOutgoingContext(ctx, "token", t) ⊢ ctxPrin ctx' who'` for a token `t` with no
  `tokenOf γ t u`. It can be stated as "the server refuses or authenticates as `tokenOf`'s user".
- a check that `uiOk_call`'s proof sketch covers the nil-bundle refresh loop (it fires the refusal
  after the last attempt).

### F8. `ReqNewNoEndpoints` cannot be proved from `New.spec`

The snippet panics if `New(Config{Logger: lg})` returns no error. `New.spec`'s post is the same
disjunction (`clientMut` or an error) whatever the endpoints. The empty list meets `cfgOk` (an empty
`[∗list]`), so the snippet's panic is not refuted. The code returns `ErrNoAvailableEndpoints`
(`client.go:87-89`), and New.lean's sketch says so.

**Fix:** add `⌜cfg.Endpoints'.len = W64 0 → c = null ∧ err ≠ GoInterface.nil⌝` (or `eps = []`
through `cfgOk`'s list) to `New.spec`'s post. `kubernetes.New.spec` inherits it.

## Second tier

- **S1. `ActiveConnection` has no snippet, and its users need more than `connOk`.** Kubernetes'
  `blockUntilReady` (`factory/etcd3.go:362-380`) calls `conn.GetState()`, `Connect()` and
  `WaitForStateChange`. No spec under `Spec/google_golang_org/grpc/` covers them, and 1c's
  `req/google_golang_org_grpc.md` does not ask for them. grpcproxy calls raw stubs on the connection
  with `grpc.WaitForReady(true)` (`grpcproxy/lease.go:84`), which needs a `callOptsOk` (or
  stub-option) introduction for grpc call options, not only retry options.
  **Fix:** a snippet `ReqActiveConnection` (`GetState` until `Ready`), and requests to 2a: the three
  `ClientConn` methods over `connOk`, and `callOptsOk` of a slice holding `WaitForReady`.
- **S2. `Endpoints` is not tied to the configuration.** `ReqEndpoints`' header claims "the configured
  ones", which `Client.Endpoints.spec` does not give and the snippet does not check. No in-scope
  user's safety depends on it: Kubernetes' compactor uses the endpoint list only to deduplicate
  compactors. **Fix:** drop the claim from the header.
- **S3. Kubernetes `OptimisticDelete` and `Count` have no snippet.** `store.go:469` deletes with a
  precondition and `GetOnFailure`; `store.go:667` counts. They have the same shape as `ReqKubeCAS` and
  `ReqKubeList`. **Fix:** one snippet each (a stale-revision delete returns the current key-value; a
  count after an owned create is at least 1).
- **S4. Documentation that misstates the code or the snippets:**
  - `lessor__Grant.lean` Changes says the old update was exclusive; it was `□ ▷ Spec`.
  - `ApiLease.lean`'s header and `lessor__KeepAliveOnce.lean` cite `clientv3lease/once.go`;
    `ReqKeepAliveOnce` is in `reads.go`.
  - `lessor__Leases.lean` cites `ReqLeasesGranted` and "a granted id listed" (F1).
  - `Client__Close.lean` cites `ReqCloseThenCalls`; the snippet is `ReqNewWrapClose`.
- **S5. `Client.Close` should take `clientRest`.** `Close` (`client.go:147-159`) never reads `KV`.
  With F2's law, a holder of `clientRest` (the proxy, a leasing client) can close.
- **S6. Small statement noise:**
  - `Auth.Triple`, `Cluster.methods`' `MemberRemove` and `MemberPromote`, and `Maint.methods`'
    `AlarmList` take `ctxPrin ctx who ∗ ctxPrin ctx who` (duplicated).
  - `Maint.methods`' `Status` post has a second disjunct (`resp = null ∗ callErr`) subsumed by the
    third (`resp = null ∧ err ≠ nil`).
- **S7. Go findings not filed.** CLAUDE.md asks that a finding be recorded at once.
  - `NewLeaseFromLeaseClient(remote, nil, t)` with a nil logger panics in the loops' `l.lg.Warn`
    (`batch-1c.md`, "Go findings": by code reading, `blocks-proof: no`). It belongs in
    `nonissues/`; it is not there.
  - `nonissues/etcd-client-dialoptions-unary-interceptor.md` should name the gRPC proxy as an
    in-tree user (F4).

## What is good

- **The update shapes follow the retry policy exactly** (`reqRetryRep` against `retry.go`), and the
  at-most-once argument rests in one place, the interceptor's `AttemptTriple` → `uiOk_call`. The
  persistent `Grant` and `Revoke` match the code; no user is hurt (see the at-most-once section
  above).
- **The keep-alive contract is honest and sufficient.** It takes no update and states nothing about
  liveness. Every value is about `id` with a positive TTL, read-only, so grpcproxy's forwarding (L4)
  and the session's draining (L3) are served. No thread token is taken, as 1d needs for sessions
  created in loops (v3lock, v3election, leasing's monitor).
- **`TimeToLive` of an unknown lease is a reply** (TTL -1, granted 0, no keys), as the handler maps
  it. This serves `leasekv`'s "about another lease" check and the proxy's forwarding.
- **`cfgOk` covers every configuration the examples and `kubernetes.New` use**, apart from the TLS
  producer (F5): user and password, `MaxUnaryRetries`, keepalive, a logger, the context, auto-sync
  with verification off.
- **The Kubernetes wrapper's contract** is one bundle over the KV shapes (`Kube.methods`). It handles
  `LeaseID` in `OptimisticPut` (L2) and `GetOnFailure`'s current key-value.
- **`clientMut_fields`** gives 1d and 1e the other five fields read-only while `KV` stays writable.

## Ranking of the targets by need of revision

1. **`ApiLease.lean` and the `lessor` specs, with `clientv3lease/`**: F1 (verified examples not
   served; snippets missing), S4.
2. **`ApiClient.lean`, `New` and the `Client.*` lifecycle specs, with `clientv3client/`**: F2, F3,
   F4, F6, F7, F8, S1, S5, S6.
3. **`client/pkg/v3/transport`**: F5 (a missing trust-boundary spec on the production path).
4. **`kubernetes/`**: S3.
5. **`credentials/`, `internal/{endpoint,resolver}`, `client/pkg/v3/{types,verify,logutil}`**: no
   finding. Their users are internal to `New`, and Kubernetes' `CreateDefaultZapLogger` is served.

## Verdict

Not done: eight first-tier findings. Two are quick for 1c: F2 (one law) and F8 (one conjunct).

- **Missing specs or snippets in this batch:**
  - F5: Kubernetes' TLS construction has no producer;
  - F6: promoted `(*Client).Status` and the other promoted non-KV methods have no spec;
  - F7: the auth example's refused principals have no snippet.
- **Waiting on a user or W0 decision**, and each needs 1c to write the snippets and the open
  question:
  - F1: per-member lease views, for three verified examples;
  - F3 and F4: a per-call principal, for the in-process client and the gRPC proxy's client.

The central design choice, repeatable `Grant` and `Revoke`, holds up: no user relies on a lease
grant being applied at most once.
