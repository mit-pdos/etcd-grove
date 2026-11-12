# Batch 2a, completeness review, round 1

Reviewer: completeness (separate from the author). Commit under review: `b5cecfd608` (2a drafts) plus
the working tree (3h's `etcdserverpb/Api.lean` modified, not 2a's). Findings formed before reading
`batch-2a.md`; where the author's report already lists an item as "left out" or "open", it is said.

Targets: the grpc boundary (`SpecPlan/Spec/google_golang_org/grpc/**`), the proto boundary
(`SpecPlan/Spec/google_golang_org/protobuf/proto/`), rpctypes (`SpecPlan/Spec/go_etcd_io/etcd/api/v3/v3rpc/rpctypes/`),
v3rpc's handlers (`SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/`, not the watch files), the
snippets `examples/specreq/{grpc,v3rpc}/` (both pass `go vet` and `gofmt -l`).

Go paths below: `S/` = `.lake/src/`; k8s = `/home/ubuntu/go/pkg/mod/k8s.io/apiserver@v0.0.0-20261021221356-9c4ec15b8038/`;
tests = `/home/ubuntu/go/pkg/mod/github.com/upamanyus/etcd/tests/v3@v3.0.0-20261107170612-a4d2bb1720b9/`.

## Users and their patterns

| # | pattern | users (one example each) | relies on | snippet |
|---|---|---|---|---|
| U1 | unary call through the generated stub (and the client's retry interceptor) | `S/api/etcdserverpb/rpc_grpc.pb.go:70-77`; `S/client/retry_interceptor.go:43-60`; tests' `kvc.Put` (59 sites) | one run per attempt; the reply's content; a status's description and **code** | `grpc/at-most-once`, `v3rpc/*` (raw stubs) |
| U2 | server-streaming client (`RangeStream`, `Snapshot`) | `S/api/etcdserverpb/rpc_grpc.pb.go:80-94`; k8s `pkg/storage/etcd3/store.go:946-960` | chunks in order, end with `io.EOF`/status; code `Unimplemented` for fallback | `v3rpc/range-stream` (Snapshot: none) |
| U3 | bidirectional client stream with a sender and a receiver goroutine (`LeaseKeepAlive`, `Watch`) | `S/client/lease.go:605-620` (`stream.Context()` in the sender) | halves used concurrently; `Context()` from either | none here (watch: 2b's) |
| U4 | dialing (`NewClient` with options) | `S/client/client.go:228-272` (keepalive, insecure creds, interceptors), k8s `storagebackend/factory/etcd3.go:309-346` (chained interceptors, stats handler, context dialer), `examples/lib/etcdstart/common.go` | each option has `dialOptAt` | none |
| U5 | building and serving the server | `S/server/etcdserver/api/v3rpc/grpc.go:41-104`, `S/server/embed/serve.go:141-290`, `examples/lib/etcdstart/common.go:192-201` | registrations, options, listener, `Serve`/`ServeHTTP` | `v3rpc/serve` |
| U6 | in-process handler calls (no grpc) | `S/server/etcdserver/api/v3client/v3client.go:33-52` via `S/server/proxy/grpcproxy/adapter/*`; used by embed's v3lock/v3election (`S/server/embed/serve.go:148-150`) | the handler's triple at the caller's own context and request | none |
| U7 | gateway (JSON → gRPC, default on: `S/server/embed/config.go:554`) | `S/api/etcdserverpb/gw/rpc.pb.gw.go:50` (`grpc.Header`, `grpc.Trailer` call options) | U1 plus those options | none |
| U8 | error classification by description | `S/client/client.go:610` (`ContextError`), `S/client/retry.go:55,92`, tests' `eqErrGRPC` (32 sites) | `rpctypes.Error`/`ErrorDesc` of a status | `grpc/status-classify`, `v3rpc/validation-answer` |
| U9 | error classification by **code** | `S/client/retry_interceptor.go:361-362` (`status.Code`), `S/client/client.go:577-584` (`isHaltErr`), `S/client/leasing/kv.go:304`, k8s `store.go:956,959`, `watcher.go:260-266,316,397`, `metrics/metrics.go:229-242` | a definite etcd error never has `Canceled`/`DeadlineExceeded`; `Unimplemented` only from the refusals | none (`status-classify` reads the code of a locally made status only) |
| U10 | comparison with rpctypes' client values | k8s `errors.go:33,64` (`err == ErrCompacted`), `store.go:923` (`errors.Is(err, ErrFutureRev)`), `S/cache/store.go:88,98`, `S/cache/watcher.go:75` (`ErrCompacted.Error()`) | `init.spec`, W0's `errorsIs_errVal` | `grpc/status-classify` |
| U11 | `Error()` of an `ErrGRPC*` status | `S/server/etcdserver/api/v3rpc/watch.go:294-303` (2b) | a non-empty string | none |
| U12 | `errors.As(err, &EtcdError)` / `err.(interface{Code()})` on a call's error | `S/client/client.go` `ContextError`, `S/client/leasing/kv.go:300`, k8s `metrics.go:229`, `watcher.go:260` | statuses are not `EtcdError`s | none |
| U13 | outgoing / incoming metadata, map index `md[k]` | `S/client/lease.go:390-394`, `S/server/etcdserver/api/v3rpc/interceptor.go:57-68,228-239`, `S/server/auth/store.go:1083-1085` | the lookup's result | `grpc/metadata-out` (outgoing, `Get` only) |
| U14 | proto `Size`/`Marshal`/`Clone`/`Merge`/`Equal` | `S/client/kv.go:105`, `S/client/compare.go:193`, interceptor `logUnaryRequestStats`, raft, 2b's fragmenting | no panic; content kept | none (owners' batches) |

## First tier

### F1. Dropped trust-boundary specs that the callers still call (grpc; "A smaller API is not a narrower scope", "Complete")

The old boundary (`specs-ref/Spec/google_golang_org/grpc/`) had trusted specs that verified proofs
used. The new one drops them, and their callers on this branch still need them. The author's report
lists some as "left out" ("each would be a neutral `dialOptAt v id`"), but no spec gives that
`dialOptAt`, so the callers cannot meet their preconditions:

| missing spec | caller that needs it (Go) | caller's spec that cites it |
|---|---|---|
| `grpc.StaticMethod()` → `callOptOk` | every generated stub: `S/api/etcdserverpb/rpc_grpc.pb.go:71,81` | 3h's `kVClient__Range.lean:5`, `watchClient__Watch.lean:5` ("2a: a `callOptOk` option") |
| `grpc.Peer(&p)` → `callOptOk` (it writes `*p` after the attempt: it needs `p`'s ownership, lent and returned) | `S/client/retry_interceptor.go:46-47`, every unary call | 1c's `Client__unaryClientInterceptor.lean` sketch ("a `peer` option") |
| `(*ClientConn).Target()` | `S/client/retry_interceptor.go:60` (logged) | 1c's `ApiClient.lean:372` (the slot's docstring) |
| `grpc.WithKeepaliveParams` → `dialOptAt v id` | `S/client/client.go:231-237` (whenever `DialKeepAliveTime > 0`: `examples/lib/etcdstart`, Kubernetes) | 1c's `Client__dialSetupOpts.lean:4` |
| `insecure.NewCredentials()` | `S/client/client.go:244` (every client without TLS) | 1c's `dialSetupOpts` (old: `credentials/insecure/NewCredentials.lean`) |
| `grpc.KeepaliveEnforcementPolicy`, `grpc.KeepaliveParams` → `srvOptAt v id` | `S/server/embed/etcd.go:777,784`; `examples/lib/etcdstart/common.go:193` | `V3rpc.Server.spec` takes `srvOptAt v id` for each `gopt` |
| `health/grpc_health_v1.RegisterHealthServer` | `S/server/etcdserver/api/v3rpc/grpc.go:98` | `Server.lean`'s sketch (see F4) |
| `status.Code(err)` | `S/client/retry_interceptor.go:362`; k8s `store.go:956,959`, `watcher.go:316,397` | 1c's `isContextError.lean:6` ("`status.Code(err)` (2a)") |
| `GenericClientStream.{Send,Recv,CloseSend,Context}`, `GenericServerStream.{Send,Recv,Context}` (grpc's generic wrappers, untranslated: `Code/google_golang_org/grpc.lean:615-623`) | the stubs' and handlers' `x.Recv()`, `stream.Send(...)`: `rpc_grpc.pb.go:86`, `S/server/etcdserver/api/v3rpc/lease.go:111,145` | 3h's req item 3 asks 2a for "the typed wrappers' `Send`/`Recv` are the stream's `SendMsg`/`RecvMsg`"; only the interface methods' laws exist |
| `ClientStream.Context()` (`cliSend`/`cliRecv` side) | `S/client/lease.go:618` (sender goroutine) | 1c's `kaSendAt_context` (req item 4) |

Fix: add a spec per row (for `Peer`, take `p ↦ _` and give it back inside the attempt's post; for
the generic wrappers, laws `srvSend_send`/`cliRecv_recv` at the wrapper value, or one spec per
wrapper method over the halves).

### F2. A definite etcd error's gRPC code is lost (rpctypes `callErr_view`, `callErr_status`; v3rpc `ansOutcome`, `etcdUnary`)

1c's `isContextError.spec` promises that `true` means indefinite. The Go code returns `true` when
`status.Code(err)` is `Canceled` or `DeadlineExceeded` (`S/client/retry_interceptor.go:362`). The
mapped definite errors' codes are never those two (`Rpctypes.code`: only `.canceled`,
`.deadlineExceeded` and `.watchCanceled` have them, and all three are unmapped). But the
vocabulary forgets the code:

* `callErr_view` gives `∃ c ok, errView err c (desc e) ok` for `.etcd e`;
* `callErr_status` builds `.etcd e` from a status with any code `c`;
* `ansOutcome`'s error case is `∃ code, o = .status code (desc e)`;
* `etcdUnary`'s second way takes `∀ code`.

So a `.etcd e` with a definite `e` and code `Canceled` is admitted, and `isContextError.spec` cannot
be proved. k8s's `isCancelError` (`watcher.go:260-266`) has the same need. Fix: pin
`c = Rpctypes.code e` in all four places. The code is true of the server: `togRPCError` sends the
`ErrGRPC*` variable, `init.spec`'s `statusErr v (code e) (desc e)`.

### F3. The lease contracts are not per member, but W0 and 1c's lease specs are (v3rpc `etcdContract`, `etcdUnary`, `servesAt_addr`)

W0's round 3 made lease reads per member. A `Grant` through `ep` gives `leaseViewLb γ ep i`, and a
`Leases`/`TimeToLive` through `ep` holding `leaseViewLb γ ep i` is answered at a table `j ≥ i` and
gives `leaseViewLb γ ep j` (`SpecPlan/Spec/go_etcd_io/etcd/client/v3/ApiLease.lean:187-216`,
`api/v3/State.lean:156-170`). These facts can only come from the server's contract, through grpc.
But `etcdContract γ` and `etcdUnary γ m` (`v3rpc/Api.lean:183-189,241`) do not depend on the
address, and their `Φ` receives only `Q σ σ' res`. So 1c's `Lease.GrantTriple` and
`LeaseRead.Triple` cannot be realized over grpc. Fix:

* make the contract `etcdContract γ ep`;
* for the lease methods, have the member give `leaseViewLb γ ep j` with the answer and take it with
  the request;
* restate `servesAt_addr` as `servesAt γ ep ⊣⊢ addrAt ep (etcdContract γ ep)`.

### F4. The real server builds cannot meet `start` (grpc `start`, `RegisterService`, `Serve`; v3rpc `Server.spec`; the U5 users)

* **Registrations outside `etcdContract`.** embed registers `v3electionpb.RegisterElectionServer`
  and `v3lockpb.RegisterLockServer` on the same server, and optionally `sctx.serviceRegister(gs)`
  (`S/server/embed/serve.go:184-187,244-247`). `v3rpc.Server` registers grpc's health service itself
  (`grpc.go:98`). `RegisterService.spec` records every registration in `B.regs`, and `regsOk B C`
  needs each `C.unary r.1 = some _`. `etcdContract γ` has no Election, Lock or Health entry, so:
  * `Server.spec`'s post `regsOk B (etcdContract γ)` contradicts the health registration;
  * embed can never apply `start`.

  The header's "registrations of grpc's own services are not in `B.regs`" has no spec behind it.
  Fix: either let `addrAt ep C` bind a contract that *extends* etcd's (`servesAt γ ep ⊣⊢ ∃ C, addrAt
  ep C ∗ ⌜C ⊇ etcdContract γ ep⌝`, with v3election/v3lock and health getting their own contracts),
  or give `RegisterService` a variant for services outside `C`.
* **Listeners that are not a plain `net.Listen`.**
  * In the default insecure mode, `gs.Serve` runs on a cmux sub-listener (`serve.go:211-213`).
  * In the default secure mode, `gs.Serve` is never called. grpc is reached through
    `grpcHandlerFunc` → `gs.ServeHTTP` (`serve.go:258-260,314-322`), from net/http's server.

  `start.spec` takes `Grpc.listenerAt lis ep`, which no spec on the branch produces (`SpecPlan/Spec/net/http`
  has its own `Http.listenerAt`, 2f). No spec covers `ServeHTTP` or cmux. Fix:
  * use one listener predicate (`Http.listenerAt`, or a shared `net` one) with an introduction for
    cmux's `Match`;
  * add `Server.ServeHTTP` consuming the same `serveTok` (or a handler fact for net/http's `Serve`).
* **The listen address versus the dialed address.** A member listens at `--listen-client-urls`
  (often `0.0.0.0:2379`), and clients dial `--advertise-client-urls`. `addrFree`/`addrAt` are per
  string, so `start`'s `ep` and the client resolver's `A ep` are different strings for one socket.
  This is the same defect as `reviews/2f-provability-1.md` F3. Grpc's `addrFree` and Http's
  `addrFree` are also two separate "one per address" resources from adequacy. Unify the address
  vocabulary with 2f.

### F5. A stream's `Context()` needs the receiving half; the handlers call it from other goroutines (grpc `srvStream_context`)

`srvStream_context.spec` takes `srvRecv st …`. Go calls `stream.Context()` from goroutines that do
not hold that half:

* `LeaseServer.LeaseKeepAlive`'s main goroutine, after handing both halves to the loop
  (`S/server/etcdserver/api/v3rpc/lease.go:94-106`);
* `watchServer.Watch` likewise (`watch.go:228-229`);
* the watch `sendLoop`, with only the send half (`watch.go:492,550,574`);
* the stream interceptor's monitor goroutine (`interceptor.go:343`);
* the client's sender (`S/client/lease.go:618`, F1).

`LeaseServer__LeaseKeepAlive.lean`'s own sketch calls it after the fork. Fix: a persistent
`srvCtxOf st ctx md` (with `rpcCtx ctx md`) given with the halves at the run's start, and
`Context()` taking only that fact.

### F6. Errors that are statuses have no `Error()` and no Go type (grpc; U11, U12)

* `(*status.Error).Error()` has no spec. `errMsg` is given only for non-statuses (`errView`), and
  `statusErr` says nothing of `Error()`. 2b asks (req item 5) for `ErrGRPC*.Error()` to be a
  non-empty string, and `watch.go:294-303` calls it. Fix: a law `statusErr err c m ⊢ errMsg err
  (grpcText c m)`, with `grpcText` non-empty (grpc's `"rpc error: code = … desc = …"`).
* `statusErr` says nothing of the dynamic type, so `errors.As(err, &EtcdError{})` and
  `err.(interface{ Code() codes.Code })` cannot be decided on a status. The callers:
  * W0's `ContextError` sketch ("`errors.As` true exactly for `errVal`s");
  * 1e's `leasingKV.acquire`;
  * W0's `errorsIs_errVal`, whose docstring cites "2a: a gRPC status's `Is` is false against an
    `EtcdError`" (that `Is` method exists: `*status.Error` has one);
  * k8s `metrics.go:229`, `watcher.go:260-263` (`GRPCStatus()`).

  Fix: a law fixing the type of a status error (grpc's `*status.Error`, with `Is` false against a
  non-status target, no `Unwrap`), and specs of its `GRPCStatus()`. (Uncertain: the exact premise
  Perennial's `errors.As` spec needs. Something about the type is needed in any case.)

### F7. `rangeStreamSpec` forbids `ErrCompacted` before the first chunk, but the server returns it there (v3rpc)

`rangeStreamSpec`'s `fin` allows the unfired compacted end only with `n ≠ 0`, and `rsSink_out` only
with `ms ≠ []` (`Api.lean:218,352`). But `EtcdServer.RangeStream` can fail with `ErrCompacted`
before sending any chunk:

* the first page is read at `headerRev`;
* if that page ends the stream (`done`), `txn.Count(..., r.Revision)` at the pinned revision runs
  *before* the first `Send` (`S/server/etcdserver/v3_server.go:249-258`);
* a compaction past `headerRev` in between makes it fail.

W0's consumer (`client/v3/Api.lean:1030-1033,1081-1082`) already allows it "possibly before any
chunk". Fix: drop `n ≠ 0` and `ms ≠ []`.

### F8. `mdAt` has no lookup law; the callers index the map (grpc `metadata`)

The Go callers index the metadata map directly:

* `md[rpctypes.MetadataRequireLeaderKey]` (`interceptor.go:68,239`: 2a's own interceptors);
* `md[TokenFieldNameGRPC]` then `ts[0]` (`S/server/auth/store.go:1083-1094`, 3d);
* `md[...]` on outgoing metadata (`S/client/lease.go:394`, 1c).

`mdAt` is opaque. Its docstring names `mdAt_index` "a law of the realization", but no such law is
stated. Fix: `mdAt_index.spec` (`md[k]` returns a read-only slice of `md.get k`, with `ok ↔ k`
present). For the incoming metadata it should also give that a present key has at least one value
(`rpcCtx`'s `md`, since grpc never decodes an empty header), which `store.go:1094`'s `ts[0]` needs.

## Second tier

1. **`msgsFit` has no supplier on the client side yet.** `NewClient.spec` takes it, but no client
   spec carries it (1c's `cfgOk`/`New.spec`, `Client__dial.lean:44`). 2a asked 1c in
   `req/..._client_v3.md` ("from 2a", item 1). This is an integration gap to track; every
   client-creating program (txnlin, k8s) inherits it. Its depth half (`depth < 10000`) is stricter
   than Go needs on the client: a deeper `Txn` is refused by the server (an error), not a panic, and
   Go panics only near the stack limit (about a million levels). Consider a separate, laxer stack
   bound ("No unneeded premise").
2. **Kubernetes' dial options are not neutral.** `WithChainUnaryInterceptor` and
   `WithChainStreamInterceptor` change what `Invoke` calls. `WithStatsHandler(otelgrpc)` adds
   `traceparent` metadata, so `mdSeen (md0 ++ mdc) md` would need it in `R` or `reservedKey`. State
   them with a pass-through premise (like `metricsOk`), not as `id`. `WithContextDialer` and
   `WithBlock` (1c req item 2) are still missing.
3. **The in-process pattern (U6) is not served.**
   * `HandlerTriple` needs `rpcCtx` and an owned request.
   * `v3client` passes the caller's request.
   * `NewMaintenanceServer(s, nil)` needs `notifierAt nil`, for which there is no law.

   2b raised the same point. Either a second instance of the handler triples at any `ctxOk` context
   and a fraction of the request (Go writes only `LeaseGrant`'s `ID` and `RangeStream`'s fields), or
   an explicit scope note. **Go bug, not yet recorded:** `v3client.New` builds
   `NewMaintenanceServer(s, nil)` (`S/server/etcdserver/api/v3client/v3client.go:46`), and
   `maintenanceServer.Defragment` calls `ms.healthNotifier.defragStarted()`
   (`S/server/etcdserver/api/v3rpc/maintenance.go:121`) on that nil interface. So
   `v3client.New(s).Defragment(ctx, ep)` panics (auth off, or as root). Nothing in `issues/` or
   `nonissues/` covers it. It belongs in `nonissues/` (found by reading; etcd itself does not call
   it) unless a Go test is written.
4. **The keep-alive reply carries nothing (`kaSpec.dn = True`).** etcd's tests rely on its `ID`
   and `TTL` (tests `integration/v3_lease_test.go`, `lac.Recv()` then `rsp.ID == lresp.ID`). The
   author lists this as open. Also, `kaSpec.up` requires `mdPrin` with no consumer (the handler's
   `LeaseRenew` takes no principal): this premise is uncertain.
5. **Client-certificate principals.** `mdPrin γ md who` reads only metadata. With
   `ClientCertAuthEnabled` a token-less request's principal is the TLS peer's CN (2b's round-1
   item). Either `mdPrin` takes the peer or `isServer` excludes the mode.
6. **The gateway (U7, on by default).** It needs the call options `grpc.Header`/`grpc.Trailer`
   (writing metadata pointers, like `Peer`) and `grpc.WithDefaultCallOptions`
   (`S/server/embed/etcd.go:817`). No batch owns the gateway; say so in the scope.
7. **`codes.Code.String()`** (k8s `metrics.go:231,234,237-242`; `codes.toml` translates constants
   only) and protoimpl's `String()` of requests (`logUnaryRequestStats`, `interceptor.go:118`) have
   no spec. The first is needed if k8s's metrics are in scope; the second is 3h's or 2a's, owner
   unclear.
8. **`sicEtcdOk` is opaque with no law**, and there is no stream form of `icChain_call`. So
   `regsOk`'s stream half has no supplier in `Server.spec` (the author lists it as open). The
   wrapper `serverStreamWithCtx` (`interceptor.go:244,313`) also needs a law carrying the halves from
   `st` to the wrapper value.
9. **`Proto.msgAt` has no fractional splitting law** (`dq1 + dq2`). Only `msgAt_persist` exists.
   W0's "any fraction, given back" and 2b's shared fragments can live with `discard`; a caller
   lending half and keeping half cannot.
10. **Snippets missing for patterns U3, U4, U9 (code-based classification), U11, U12, U13 (incoming
    metadata and principal), U6.** `v3rpc/serve` passes no `gopts` and serves a plain listener, so
    it misses F1's `KeepaliveEnforcementPolicy` and F4's registrations and listeners, which embed
    and `etcdstart` need.

## What is good

* **grpc.**
  * The message model is content-valued and owner-related (`msgAt`/`Content`), so there is no
    caller-built model.
  * The urpc-style `UnarySpec` with at-most-once per attempt (`attemptOk_call`) is exactly what
    1c's `AttemptTriple` needs.
  * `addrAt` is persistent and agreeing, which keeps restarts sound.
  * The workload premise sits on the producers, following `reply-size.md`.
  * `notSent` is checked against grpc-go v1.84 and found dead (`retry.go:93`).
* **rpctypes.**
  * The description, code and mapped table is transcribed whole, and the unmapped six are found.
  * `Error.spec` returns the exact result.
  * `callErr`'s realization by view and introductions serves W0's `ContextError`, 1e's
    `Unimplemented` and k8s's `err == ErrCompacted` / `errors.Is(ErrFutureRev)` (with
    `init.spec`'s `errVal e` values).
* **v3rpc.**
  * There is one contract per method across modes, and validation errors are model answers.
  * `LeaseTimeToLive`'s not-found reply is modelled (`ansOutcome`).
  * The quota refusal is `.noSpace` instead of a premise.
  * The interceptors' early refusals (`ErrGRPCNotCapable`, `ErrGRPCNoLeader`,
    `ErrGRPCInvalidClientAPIVersion`, `interceptor.go:49-71`) all fall in `etcdUnary`'s second or
    third way (checked against `EtcdErr.indefinite` and `mapped`).
* **proto.** Every proto use in the client and server listed by the batch has a spec, with the depth
  and size premises explained by the code (`Marshal`'s allocation, decode's recursion limit).

## Targets ranked by need of revision

1. **grpc boundary**: F1 (ten missing specs), F4 (registrations, listeners, addresses), F5, F6, F8;
   second tier 1, 2, 6, 7, 9.
2. **v3rpc**: F3 (per-member lease contract), F4 (`Server.spec`'s post), F7; second tier 3, 4, 5, 8.
3. **rpctypes**: F2 (pin the code), and its share of F6.
4. **proto**: second tier 9 only.
5. **snippets**: second tier 10.

## Verdict

Not complete. Eight first-tier findings:

* F1, F4, F5, F6 and F8 leave real callers unable to establish a precondition or get a needed
  fact: every stub call, every unary call through the client's interceptor, every keepalive client,
  embed's and `etcdstart`'s server, the lease and watch stream handlers.
* F2 and F3 make 1c's `isContextError` and W0/1c's per-member lease specs unrealizable over the
  contract.
* F7 makes `rangeStreamSpec` false of the server's `RangeStream`.

All are repairable inside the batch's vocabulary, except F4's address and listener unification,
which needs 2f and 2e. One Go bug was found (second tier 3, the `v3client` Defragment nil-notifier
panic), to be filed in `nonissues/`.
