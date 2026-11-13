# k8s 7f-4: enumeration and the trusted package (Freeze draft, 2026-11-12, branch `k8s-7f4`)

Steps 1-2 of `notes/k8s-7f4-rebaseline.md` §4 (approved by etcd-grove-81, Q-RB1..4). Against lean
`802c4824aa`. §2 is the trusted package as text; it is to be written into Lean (definitions and the
changed axiom statements, building, no proof changes beyond what keeps the build green) and then
**stops for 81's independent review** before anything uses it.

## 1. Enumeration (step 1)

### 1a. The auth path (Q7f4-3): T2 by deletion

- `isReqAuth st RD` (`etcdserver/InvRequest.lean:2633`) and `isReqAuthBound` take
  `mvcc.txnCtx ctx cd ∗ context.libCtxOk ctx (∗ RD)` in each triple.
- Their realizers ignore `txnCtx`: `isReqAuth_of_authInv`/`isReqAuthBound_of_authInv`
  (`AuthReqDerive.lean:122, 136, 156`: `⟨-, #Hlib, Hrd⟩`), over `authStore.AuthInfoFromCtx`
  (`incomingCtxOk`) and `AuthInfoFromTLS` (`peerCtxOk ∗ incomingCtxOk`).
- **But** `auth.NewAuthStore`'s axiom (`Proof/go_etcd_io/etcd/server/v3/auth/NewAuthStore.lean:26`)
  posts `isReqAuth st RD` directly (auth off). Dropping `txnCtx` from `isReqAuth` strengthens that
  axiom's post: a trust-base change (§2, T-e). True in Go: `AuthInfoFromCtx`/`AuthInfoFromTLS` read
  only the metadata and the peer (`Value` at grpc's keys), never `Done`/`Err`.
- Consumers on the stream paths: `serverWatchStream.isWatchPermitted` (W3; gets `libCtxOk` from
  `grpcRunCtx`, `serverWatchStream__isWatchPermitted.lean:60`) and `checkLeaseRenew` (L5; its spec
  takes `txnCtx ∗ libCtxOk`, an internal spec whose `txnCtx` then goes too).

### 1b. What the stream paths use of the run context

`srvStreamIs`'s last conjuncts are destructured as `#Hctxis` (`isContext ci cd`) and `#Hrunctx`
(`grpcRunCtx ci`) in `watchServer__Watch.lean:192`, `serverWatchStream__recvLoop.lean:212`,
`serverWatchStream__sendLoop.lean:1600`, `LeaseServer__leaseKeepAlive.lean:168`,
`LeaseServer__LeaseKeepAlive.lean:35`. Uses:

| Path | Uses | Of `grpcRunCtx`'s parts |
| --- | --- | --- |
| `recvLoop` (W4/W5) | `Tracer.Start(ci)` with `txnCtx` (`iright Hctxis`), its `isContext` wand, its `spanCtxOk` wand on `spanCtxOk_of_runCtx` (`:455-459`); then mvcc's `Watch` on `isContext ∗ spanCtxOk` of the traced context | `spanCtxOk` |
| `isWatchPermitted` (W3) | `AuthInfoFromCtx` through `isReqAuth` | `libCtxOk` |
| `leaseKeepAlive` (L3) | `LeaseRenew(ci)`: `isContext ∗ libCtxOk` (`:191-192`) | `libCtxOk` |
| `LeaseRenew` (L4-L7) | `Tracer.Start(ctx)` → `ctx1`; `context.wp_WithTimeout ctx1` (needs `isContext ctx1`); `checkLeaseRenew(ctx1)` (`txnCtx ∗ libCtxOk`); `waitLeader(cctx)`, `RenewHTTP(cctx)` (`isContext`) | via `Tracer.Start`'s `libCtxOk` wand |
| `Watch`, `sendLoop`, `LeaseKeepAlive` | `Done`/`Err` only (`#Hctxis`) | none |

The etcd-keys part of `grpcRunCtx` (`Value` at etcd-prefixed keys is nil) is used by no stream path.
So the weak stream end carries `srvCtxWeak ∗ libCtxOk ∗ trace.spanCtxOk` of `ci'` (R-1).

### 1c. The deletion of `runsNoRequireLeader` (step 6)

`etc/importers.py --uses runsNoRequireLeader Proof/.../v3rpc/InvStreamInterceptor.lean --files`
(2026-11-12): the 26 files of the re-baseline's table; the closed theorems are those reaching
`etcdstart.commonPremises`, `putget3`'s premises or `ServeFromStart`. Regenerate the list (with
`etc/tcb-report.py`'s roots) at step 6.

## 2. The trusted package (step 2): as written in Lean (2026-11-12)

Written into Lean on branch `k8s-7f4` (commit in the handoff). Each item: where it is, what it says,
why it is true in Go, the Go evidence (`examples/premisefix/streamctx/streamctx_test.go`, run at the
pins with GOWORK=off; at go1.27.3, the pinned toolchain, since Revision 1), and what the review should check. T-d (F2) is deferred to
7f-3 (decided by etcd-grove-81, 2026-11-12). "Stronger post" = an axiom gives more; "weaker pre" =
an axiom asks less.

### T-a. The raw stream end carries the run context's library facts in the chain form (R-1)

- **Vocabulary** (`Proof/context/LibKeysChain.lean:64` `context.libCtxOkC`, `:77`
  `trace.spanCtxOkC`; persistent): `libCtxOk`'s facts at grpc's three keys (incoming: one value
  `v`, `incomingRes v`; outgoing: `outgoingCtxOkC`; peer: `peerRes`) and `spanCtxOk`, each with
  Perennial's `ctxValue` (the chain) in place of the WP form. Otel's key only in `spanCtxOkC`
  (`spanRes`'s `otelSpan → isSpan` has no law).
- **Text** (`Proof/google_golang_org/grpc/InvGrpcStream.lean:400-423`, `srvRawStreamIs`): the last
  conjuncts are now `isContext ci cd ∗ grpcRunCtx ci ∗ context.libCtxOkC ci ∗ trace.spanCtxOkC ci`.
  The unary arm (`grpcAccepted`'s, `grpcRunCtx`) is untouched.
- **Stronger post** of grpc's `acceptRun` (stream arm, through `grpcAccepted`,
  `InvGrpcRun.lean:157`) and of `grpc_prometheus.ServerMetrics.StreamServerInterceptor` (its
  handler's `st'` has the same `ci`).
- **Go:** grpc v1.84.0 builds a stream's context as `Background()` (`server.go:1024`) →
  `SetConnection`, `peer.NewContext` (`server.go:1072-1073`, `WithValue`) → otelgrpc's `TagConn`
  (identity) → the transport's `WithTimeout`/`WithCancel` (`http2_server.go:537-539`) →
  `NewIncomingContext` (`:544`) → `contextWithServer`, otelgrpc's `TagRPC` (`extract`: the
  propagators' `WithValue`s; `tracer.Start`: `ContextWithSpan`) → `NewContextWithServerTransportStream`
  (`server.go:1306`) → `newContextWithRPCInfo` (`:1429`); prometheus's wrapper returns that
  context unchanged. All `*valueCtx`/`*cancelCtx`/`*timerCtx` over `backgroundCtx`, which
  `context.value()` walks.
- **Evidence:** `TestRunCtxChain` walks `ss.Context()`'s links by reflection, with/without
  grpc-prometheus, otelgrpc's stats handler (SDK tracer) and a client deadline: every link is one of
  the four types, ending at `context.backgroundCtx` (7-11 links).
- **Review point (from the previous agent):** no link of another type in grpc's server context
  chain. Two paths not covered by the test: `EnableTracing` (`newTraceContext`, x/net/trace's
  `NewContext`, a `WithValue`) and the `pprof.WithLabels` label path (a `WithValue`), both off by
  default; and grpc's `ServeHTTP` (`server.go:1152`, net/http's request context, standard types too,
  and `handler_server.go`'s `WithCancel`/`WithTimeout`), which etcd uses when gRPC and HTTP share a
  TLS port (transport is low priority).

### T-b. F1-general: the incoming metadata is a function of `Value(mdIncomingKey{})` (R-2) — REFUTED, dropped; replaced in Revision 1 (B1)

- **Text** (new axiom, `Proof/google_golang_org/grpc/metadata/Incoming.lean:51`):

```lean
axiom metadata.incomingOf_of_value (c c' : GoInterfaceOk) (v : GoInterface) :
    context.valueAt (GF := GF) c metadata.mdIncomingKeyAny (· = v) ∗
      context.valueAt c' metadata.mdIncomingKeyAny (· = v) ⊢
    ⌜metadata.incomingOf (GoInterface.ok c) = metadata.incomingOf (GoInterface.ok c')⌝
```

  (`Incoming.lean` now imports `Proof.context.LibKeys` for `valueAt`.)
- **Go:** `FromIncomingContext` (grpc v1.84.0 `metadata/metadata.go:268-282`) is
  `ctx.Value(mdIncomingKey{}).(MD)` then a lower-cased copy: a function of that value; `(nil,
  false)` for a non-`MD`. The `MD` the transport stores is never written after (`transportMD`).
- **Evidence:** `TestIncomingOfValue`: in a real handler (prometheus + otelgrpc), the handler's
  metadata equals (`DeepEqual`) that of etcd's wrapper over `WithCancel(ss.Context())` after
  `Cancel(ErrGRPCNoLeader)`, of a context whose `Done`/`Err`/`Deadline` panic and whose `Value`
  delegates, and of a `WithValue` child; two unrelated contexts holding the same `MD` value agree;
  two with nothing at the key both give `(nil, false)`.
- **Review point:** it concludes only from equal values (both `valueAt ... (· = v)` with the same
  `v`); nothing equates contexts whose values differ. It inherits the header's assumption that a
  stored `MD` is not mutated after (true of the transport's; a program's own `NewIncomingContext`
  with a map it mutates later would already break "`incomingOf` is a function of the context").

### T-c. F3: the raw stream is a comparable map key (Draft §6 R1)

- **Text** (`InvGrpcStream.lean:379` `rawStreamKeyTy t := ∃ t', t = go.GoType.PointerType t'`;
  `:403` `srvRawStreamIs`'s `∃ si, ⌜st = GoInterface.ok si⌝ ∗ ⌜rawStreamKeyTy si.ty⌝ ∗ …`).
  **Form decided (narrower than the text draft):** a pointer type only, not "or a named struct of
  interfaces and pointers": grpc-prometheus passes `&monitoredServerStream{…}`, a pointer
  (go-grpc-middleware v2.3.4 `interceptors/server.go:36`), not the struct.
- **Stronger post** of `acceptRun` (grpc passes `ss := &serverStream{…}`, `server.go:1307`) and of
  prometheus's contract.
- **Evidence:** `TestRawStreamKey`: at the last interceptor's position (etcd's) and in the handler,
  `*grpc.serverStream` without prometheus, `*interceptors.monitoredServerStream` with it; both are
  pointers and work as `map[grpc.ServerStream]int` keys, alone and inside a
  `serverStreamWithCtx{ServerStream, *cancellableContext}`.
- **Review point:** prometheus's wrapper type (above). Etcd's chain has no other stream
  interceptor (`v3rpc/grpc.go`: `[serverMetrics.StreamServerInterceptor(), newStreamInterceptor(s)]`;
  otelgrpc is a stats handler, it wraps no stream).

### T-e. `NewAuthStore`'s request side without `txnCtx` (§1a)

- **Text** (`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvRequest.lean:2636-2668`): `isReqAuth`'s
  two triples and `isReqAuthBound`'s are `∀ ctx, {{ context.libCtxOk ctx ∗ RD }}` (resp. `{{
  context.libCtxOk ctx }}`): the `mvcc.txnCtx ctx cd` conjunct and the `cd` binder are gone.
- **Stronger post** of `auth.NewAuthStore` (axiom, auth off). Its realizers never used `txnCtx`
  (`AuthReqDerive.lean`). The derived internal lemmas `isReqAuthBound_ctx`, `isReqAuth_ctxM` keep
  their `txnCtx`-taking statements for now (weaker; they drop it); step 5 strengthens them for W3/L5.
- **Go:** `AuthInfoFromCtx`/`AuthInfoFromTLS` (fork `673da07c8f` `server/auth/store.go`) read only
  the metadata and the peer, never `Done`/`Err`/`Deadline`.

### T-e'. `isReqAuth` takes the context's `Done()` fact (decided by etcd-grove-81, 2026-11-12; built in Revision 1)

- **Vocabulary** (new module `Proof/go_etcd_io/etcd/server/v3/auth/CtxDone.lean`, imports only
  Perennial's context proofs): `auth.ctxDoneAny ctx := □ {{ True }} ctx.Done() {{ ch, RET #ch;
  ⌜ch = chan.nil⌝ ∨ ∃ s γch, context.isContextDone s ch γch }}`, and `auth.ctxDoneAny_of_isContext`.
  Laws: `auth.ctxDoneAny_of_srvCtxWeak` (`SrvCtxWeak.lean`), `auth.ctxDoneAny_of_txnCtx`
  (`InvRequest.lean`, `doneNil` → nil, `isContext` → its `#HDone`).
- **Text:** `isReqAuth`'s two triples and `isReqAuthBound`'s take `context.libCtxOk ctx ∗
  auth.ctxDoneAny ctx (∗ RD)`. Relative to lean this is still a **stronger post** of
  `auth.NewAuthStore` (it asks `ctxDoneAny` where lean asks `txnCtx`, which gives it); relative to
  T-e, a weaker one.
- **Go:** `isValidSimpleToken` selects on `ctx.Done()`, which Go evaluates on entry
  (`notes/auth-validspec-false.md`); nil blocks that case forever, a context's Done channel is
  received on with `isContextDone`'s spec. The auth stage S1 reuses the definition.
- Status: `CtxDone.lean` and `SrvCtxWeak.lean` checked with `etc/lean-check.py` (0 errors);
  `InvRequest`, `AuthReqDerive`, `AuthInfoFromCtx` edited but not built (waiting for the review).

### T-f. The weak handler context and the three weakened trust-boundary premises (Draft §2, §4)

- **Vocabulary** (new module `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/SrvCtxWeak.lean`;
  imports only Perennial's context proofs and the generated `rpctypes`): `noLeaderErr err` (`:40`,
  the value of `rpctypes.ErrGRPCNoLeader`); `srvCtxWeak c s` (`:59`); the law
  `srvCtxWeak_of_isContext : isContext c s ⊢ srvCtxWeak c s` (`:98`, proved).
  **Form decided, stronger than the Draft's §2:** `srvCtxWeak` is Perennial's `isContextDef` with
  only its two `Err` clauses weakened (`#HErr`: `Err()` returns any value; `#HErrDone`: after
  `ContextClosed`, `err ≠ nil` and `isCtxErr err ∨ noLeaderErr err`); the other clauses
  (`#HDeadline`, `#HDone`, `#HValue` at `&cancelCtxKey`, `#HDoneFresh`, `#HParentCC`,
  `#HClosedchan`) are `isContext`'s. Why: `LeaseRenew` calls `WithTimeout(ctx1)` on
  `Tracer.Start`'s context, and `WithDeadline`/`propagateCancel` call the parent's `Deadline`,
  `Done`, `Value(&cancelCtxKey)` and `parentCancelCtx`: with only the Draft's three clauses, no
  local `WithTimeout` lemma over a weak parent could be proved through `Tracer.Start`'s post. The
  extra clauses are true of the wrapper (promoted from its embedded `WithCancel(ci)` child) and of
  a `valueCtx` over a weak context (delegated). This only strengthens the vocabulary: `waitLeader`'s
  and `RenewHTTP`'s premises ask more than with the Draft's form; `Tracer.Start`'s wand claims
  more, by delegation. (No `isTypedErr` in `#HErrDone`: `ErrGRPCNoLeader`'s typing is not
  available; step 5's lemma will tell whether it is needed.)
- `traceutil.Tracer.Start.spec` (`Spec/go_etcd_io/etcd/pkg/v3/traceutil/Tracer__Start.lean:66-84`):
  pre `mvcc.txnCtx ctx cd ∨ srvCtxWeak ctx cd` (**weaker pre**); in the post the `txnCtx` of `ctx'`
  becomes `□ (mvcc.txnCtx ctx cd -∗ mvcc.txnCtx ctx' {cd with Values := vs})` (it has to be a
  wand now that the premise may be the weak one), and `□ (srvCtxWeak ctx cd -∗ srvCtxWeak ctx' cd)`
  is added (**stronger post**). The old triple is a proved corollary,
  `traceutil.Tracer.Start.spec_txn` (`Proof/go_etcd_io/etcd/pkg/v3/traceutil/StartLaws.lean:30`),
  which the nine callers now apply (one token each). Go: `ContextWithSpan(ctx, s)` is a
  `WithValue`, or the no-op tracer returns `ctx` itself. The spec's open note (isSpan for every
  `txnCtx`) is not widened: the weak contexts passed are children of grpc's run contexts.
- `EtcdServer.waitLeader.spec` (axiom; `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__waitLeader.lean:47`):
  `srvCtxWeak ctx cd` in place of `isContext ctx cd` (**weaker pre**). Go: it only selects on
  `ctx.Done()` (`v3_server.go:785-803`).
- `leasehttp.RenewHTTP.spec` (axiom; `Spec/go_etcd_io/etcd/server/v3/lease/leasehttp/RenewHTTP.lean:58`):
  `srvCtxWeak ctx cd` in place of `isContext ctx cd` (**weaker pre**). Go: net/http's transport
  works on its own `context.WithCancelCause(req.Context())` (go1.27 `net/http/transport.go:675`);
  HTTP/2 reads `ctx.Err()` only after `ctx.Done()`, but for `shouldRetryDial`'s nil test
  (`internal/http2/client_conn_pool.go:284`). **Evidence:** `TestRenewHTTPErrTiming`: `RenewHTTP`
  over a `*http.Transport` with a context whose `Err()` panics before `Done` and returns
  `ErrGRPCNoLeader` after: the successful call and the cancelled call (blocked server, then cancel)
  do not call `Err()`; the cancelled call returns a `*url.Error` of `context.Canceled`. (Corrected
  after the T-g review's M1: on a context already done when `RenewHTTP` is called, the transport's
  `WithCancelCause` calls the caller's `Err()` twice, synchronously on the caller's goroutine, in
  `propagateCancel`'s already-done arm and in `Cause`, go1.27.3 `context.go:487, 290`; the test's
  pre-cancelled case checks it, and that a `*url.Error` is returned. The weak pre still suffices:
  any error is accepted by the post, and each call is on a live goroutine, Addendum T-f'.)
- **Review point (from the previous agent):** net/http's `Err()` vs `Done`: above. Remaining: the
  post `applyErrIs err` for a `*url.Error` wrapping `ErrGRPCNoLeader` (reachable only if the
  derived context took the parent's `Err()` through propagateCancel's goroutine path, which a
  wrapper whose `Value(&cancelCtxKey)` is its inner `*cancelCtx` does not take); the old text
  already claims `applyErrIs` of every `*url.Error` the client returns. The `srvCtxWeak` form
  decision above.

## Revision 1 (2026-11-12, after 81's review: NOT READY)

The review's findings (two reviewers; `wf_842ada2f-10d`), what changed for each. All decided by
etcd-grove-81 (questions.md).

### B1 (blocker): T-b refuted; per-constructor preservation in its place

- **Refutation (both reviewers):** `valueAt` is a partial-correctness WP, so a program context
  `loopCtx` whose `Value` loops has `valueAt L k (· = v)` for every `v`; T-b applied through `L`
  equated every two contexts' `incomingOf` (a handler comparing `FromIncomingContext(ctx)` with
  `FromIncomingContext(Background())` panics in Go and was provable). T-b was used by nothing; it was
  dropped in the handoff commit (`58fbe131d4`).
- **Every use of `incomingOf`** (`etc/importers.py --uses incomingOf`, 2026-11-12): its definition
  (`metadata/Incoming.lean`); `FromIncomingContext.spec` (post); `context.WithValue.spec`,
  `Tracer.Start.spec`, `EnsureTrace.spec` (posts preserving it); auth's `ctxTokenOf`
  (`auth/InvAuth.lean:675`), hence `ctxBound`/`isReqAuthBound` and the request path's
  `infoBoundM`; the unary handlers' specs (`_KV_*`, `_Auth_*`, `_Lease_LeaseGrant`, `quotaKVServer`,
  `UnaryHandlerLemmas`, `InvGrpc`'s `grpcHandlerOkMd`/`grpcSrvChain`) and their `Results.lean`
  rewrites; `ReqOn`, `EtcdServer__{Put,Txn,LeaseRenew}` (the transfer through `Tracer.Start`);
  `client/.../ClientAuth.lean` and `Outgoing.lean` (delivery); the stream contracts
  (`InvGrpcStream`'s `grpcStreamMethodOk`/`grpcStreamRunOk`, `InvGrpcRun`, `_Watch_Watch_Handler`).
- **Choice:** (a) indexing the handler side by the stored value would re-index auth's token
  binding (`ctxTokenOf`/`isReqAuthBound`, which the unary path shares) and `FromIncomingContext`'s
  post: past the stream path. (b) per-constructor preservation stays on it: **(b)**.
- **Text (trusted, new):**
  - `metadata.incomingOf_cancelCtx` (`Proof/google_golang_org/grpc/metadata/Incoming.lean`):
    `ctxField c ↦□ p ⊢ ⌜incomingOf (*cancelCtx c) = incomingOf p⌝`. Go: `(*cancelCtx).Value(key)`
    at a key other than `&cancelCtxKey` is `value(c.Context, key)`, which answers as `p.Value(key)`;
    `FromIncomingContext` is a function of `Value(mdIncomingKey{})`.
  - `v3rpc.incomingOf_cancellableContext`
    (`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/WrapperMd.lean`):
    `ccField l ↦□ c ⊢ ⌜incomingOf (*cancellableContext l) = incomingOf c⌝`. Go: `Value` is promoted
    from the embedded `Context` field, written only by `newCancellableContext`'s literal
    (`interceptor.go:270-283`).
- **Proved, not trusted** (same file): `v3rpc.incomingOf_wrapper` (the composition: the wrapper over
  `WithCancel(ci)` has `ci`'s metadata); `v3rpc.wp_WithCancel_cancelCtx` (Perennial's
  `wp_WithCancel_any`, restated from the same linked specs with the child's location and
  `ctxField c ↦□ parent` in the post, which Perennial's statement hides; no Perennial change).
- **Why a looping `Value` cannot equate two contexts** (shown in the package: `incomingOf_cancelCtx`'s
  docstring, `incomingOf_cancelCtx_parent_unique`, `v3rpc.incomingOf_cancellableContext_field_unique`):
  the premises are persistent points-tos of one Go type's field, not WPs, and a points-to determines
  its value, so each `*cancelCtx` or wrapper is related to exactly one context, its field's. The
  equations follow parent links only: two contexts are equated only on one chain of such links to a
  common root. `loopCtx` is a root (not a `*cancelCtx` or a wrapper), equated only with the links
  built over it, whose `Value` loops too; grpc's run context and `Background()` are distinct roots.
  The model: `incomingOf x` is `FromIncomingContext`'s result at the root reached from `x` by these
  fields (immutable once the context is returned), arbitrary where it never returns.
- **Use (later, step 3 of §4):** `newStreamInterceptor`'s weakening contract gets
  `⌜incomingOf ci' = incomingOf ci⌝` from `v3rpc.incomingOf_wrapper`, with `ccField l ↦□` from
  `newCancellableContext`'s allocation and `ctxField c ↦□ ci` from `v3rpc.wp_WithCancel_cancelCtx`.
- **Evidence:** `TestIncomingOfValue` also compares the `WithCancel` child alone (go1.27.3: passes).

### M1 (spec lens) and m3: `libCtxOkC` covers otel's key; the chain form gives the WP form

- `context.libCtxOkC` (`Proof/context/LibKeysChain.lean`) gains
  `ctxValue ctx trace.spanKeyVal trace.spanRes`: the chain form of all four parts of `libCtxOk`.
  **Stronger post** of `acceptRun`'s stream arm and of prometheus's contract (through
  `srvRawStreamIs`); no new claim: `grpcRunCtx` already asserts `spanValOk ci` (the same value), and
  the run context is the chain T-a's test walks.
- m3, by laws (proved): `context.libCtxOk_of_libCtxOkC`, `trace.spanCtxOk_of_spanCtxOkC` (with
  `isPkgInit context`): `grpcRunCtx`'s `libCtxOk`/`spanCtxOk` parts on the stream arm follow from the
  chain forms, so they claim nothing more. `grpcRunCtx` stays whole (the unary arm shares it).
  Also `context.libCtxOkC_from`, `trace.spanCtxOkC_from` (carried by `ctxValueFrom`), for step 3.

### M1/M2 (axiom lens): T-e' built, `isReqAuth`'s docstring corrected; m1 recorded

- T-e' as drafted (above), built. The docstring now says: auth off, `AuthInfoFromCtx` returns at
  `!as.IsAuthEnabled()` (`store.go:1073`) and `AuthInfoFromTLS` reads the peer and the metadata; auth
  on with a simple token, `isValidSimpleToken` selects on `ctx.Done()` (`simple_token.go:239-243`).
- m1: the whole `libCtxOk` is kept, with the reason in the docstring and `notes/decisions.md`
  (every caller carries it; the request path's internal specs take the same fact).

### M2 (axiom lens): `Tracer.Start` takes `trace.spanCtxOk ctx`

- `traceutil.Tracer.Start.spec`: pre `(txnCtx ∨ srvCtxWeak) ∗ trace.spanCtxOk ctx` (**stronger pre**
  of the axiom); the Open note is deleted (it was this refutation) and the audit row
  (`notes/audit.md:434`) records it. `spec_txn` takes it too. Callers: the KV/lease request paths
  (`Put`, `Txn`, `DeleteRange`, `Compact`, `LeaseGrant`, `LeaseRevoke` already took `spanCtxOk`);
  `EtcdServer.Range.spec` and `EtcdServer.LeaseRenew.spec` gain it (internal specs; their callers
  `kvRangeOk_of_serverM` and `raftLeaseRenew_of_server` have it from `srvCall`/the contract), and so
  does the contract `v3rpc.raftLeaseRenew` (its user `leaseKeepAlive` from `spanCtxOk_of_runCtx`);
  `recvLoop` from `spanCtxOk_of_runCtx`. **Exported text changed** (decided by etcd-grove-81, as
  premise fixes 8's `libCtxOk` on the same results): `range_linearizable` and `range_serializable`
  (`Proof/go_etcd_io/etcd/server/v3/etcdserver/Results.lean`) take `trace.spanCtxOk ctx`. No other
  result's statement changes: no `Results.lean`/`MainLinked.lean` of the examples changed (the
  `*_safe` theorems), nothing uses the two range results, and `raftLeaseRenew_server`'s text is
  unchanged (its contract asks one more premise of its user, discharged inside `leaseKeepAlive`
  from the run context).
- m2: the disjunction stays, recorded as a known departure (`notes/decisions.md`, "k8s 7f-4
  Revision 1"); the docstring's "not widened" is made precise (`srvCtxWeak` admits program contexts
  `txnCtx` did not, but `isContext`'s arm already admitted the same kind; with `spanCtxOk` required
  neither reaches the refutation).

### Minors

- m1 (axiom lens): `srvRawStreamIs` and `grpcRunCtx` state etcd's configuration: no
  `GRPCAdditionalServerOptions` adding stream interceptors or stats handlers (`embed/etcd.go:789`).
- m2/m5: the evidence reruns at go1.27.3 (all four tests pass, 2026-11-12). The already-cancelled
  `RenewHTTP` case is not added (optional; the post accepts every error).
- m4: the collections whose roots reach `acceptRun` or prometheus's axiom: below ("Checks run,
  Revision 1").
- m3 (axiom lens, `Value(&cancelCtxKey)` determinism): no change (a Perennial question shared with
  `isContext`; noted by the reviewer as not a finding).

## Revision 2 (2026-11-12, after 81's re-review: B1/T-e'/gates READY; one blocker)

- **Blocker (axiom lens, verified):** Revision 1's `trace.spanCtxOk ctx` did not exclude the
  `Tracer.Start` refutation: `isSpan` covers only `End`/`AddEvent`/`RecordError`, the no-op tracer
  calls `SpanContext()` and `IsRecording()`. Go: `examples/premisefix/tracerspan` (`TestStartRefutes`
  reproduces the panic under a `doneNil` context and under `ContextWithSpan(Background(), …)`;
  `TestStartOtelSpans`: nil and otel's own spans return; go1.27.3). It predates 7f-4.
  **Fix:** the premise takes `trace.spanValOk ctx` (nil or `trace.otelSpan`; its docstring now lists
  `IsRecording`; `otelSpan` is an opaque trusted predicate whose producers, grpc's run context and
  otel's tracers, give otel's own span types, each of whose methods returns). `spec_txn` takes
  `context.libCtxOk ctx`, which every caller carries, and projects `spanValOk`. Reverted to lean's
  text: `range_linearizable`/`range_serializable` (no exported statement changes now),
  `EtcdServer.Range.spec`, `EtcdServer.LeaseRenew.spec`, `v3rpc.raftLeaseRenew`. History restored:
  `notes/audit.md` (refuted until this fix), `notes/decisions.md` ("k8s 7f-4 Revision 2").
- m1 (gates): `auth.ctxDoneAny`'s binder renamed `sDoneAny`; the ten entries keyed on
  `7:sDoneAny:context.ContextDesc(IPropGF)`. (The script's rule-7 key has no occurrence kinds; noted,
  not changed.) m2: `etcd_noRefusal`'s entry says its walk is truncated.
- m1 (axiom): `incomingOf_cancelCtx`'s docstring: written once for an `isContext` parent
  (`#HParentCC` excludes the `afterFuncer`/`stopCtx` rewrite). m2: the per-execution reading sentence
  (the same as `WithValue.spec`'s `incomingOf` post).

## Addendum T-f' (2026-11-12): the weak context's `Err` pays a level token (decided by etcd-grove-81, option (A))

- **Why** (step 4's blocker, `notes/k8s-7f4-handoff.md` "Steps 3-4, third agent"): etcd's wrapper's
  `Err` (fork `673da07c8f` `server/etcdserver/api/v3rpc/interceptor.go:297-304`) takes
  `c.lock.RLock()`. Perennial's `RLock` (`sync.RWMutex.wp_RLock_of`) needs a reader token
  (`ownRWMutex rw P`; `2^30 - 1` per lock, the bound below which Go's reader counter does not
  overflow). T-f's `"#HErr"`/`"#HErrDone"` gave a persistent `Err` triple with no resource, which no
  finite stock of reader tokens can pay for (unboundedly many concurrent callers), so
  `srvCtxWeak (ccCtx l)` was not provable. The bounds plan's answer (`notes/bounds-plan.md`): a reader
  pays with its thread token, through a thread pool of the lock's reader tokens
  (`init_RWMutex_threadPoolL`).
- **Text** (`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/SrvCtxWeak.lean`): new
  `abbrev v3rpc.ctxErrLvl : Nat := 4`; `"#HErr"` is
  `□ ∀ Φ, levelTok v3rpc.ctxErrLvl -∗ ▷ (∀ err, levelTok v3rpc.ctxErrLvl -∗ Φ #err) -∗ WP Err()`,
  and `"#HErrDone"` takes `levelTok v3rpc.ctxErrLvl` after `ContextClosed` and returns it with the
  error. The other clauses are unchanged. `srvCtxWeak_of_isContext` still holds (an `isContext`'s
  `Err` needs no token; it is passed through) and `auth.ctxDoneAny_of_srvCtxWeak` is untouched.
- **The level** (from `Proof/google_golang_org/grpc/InvGrpcRun.lean`): grpc's run splits its thread
  token into levels 0-3 and `threadTokFrom 4` (`threadTok_levels0123`): level 0 is the handler's own
  (the lessor's and leases' pools, `lessorLvl = leaseLvl = 0`), 1 `raftPoolN`, 2 the revoke pools
  (`srvRevokeInnerN`/`srvRevokeOuterN`), 3 `srvRunN` (`grpcStreamRunOk_of_pools`). No pool of the
  repository is at a level above 3 (`isThreadPoolL` and `levelTok` occurrences, 2026-11-12). Level 4
  is in the run's `threadTokFrom 4`, which it keeps: the wrapper's handle work hands `levelTok 4` to
  the handler with its bundle (`threadTokFrom 4 ⊣⊢ levelTok 4 ∗ threadTokFrom 5`), and a forked
  goroutine keeps the whole token `wp_fork_tok` gives it.
- **Effect on the trust base** (weaker premises, so stronger axioms): the `Err` part of the premise
  of `EtcdServer.waitLeader.spec` and `leasehttp.RenewHTTP.spec` (both take `srvCtxWeak ctx cd`), and
  of `Tracer.Start.spec`'s premise and wand (`txnCtx ∨ srvCtxWeak`, `□ (srvCtxWeak ctx cd -∗
  srvCtxWeak ctx' cd)`). Their statements are textually unchanged; each docstring has a T-f' sentence.
- **Go:**
  - `waitLeader` (`v3_server.go:785-803`) only selects on `ctx.Done()`; it never calls `Err()`, so
    a premise whose `Err` needs a token it does not have is never exercised.
  - `RenewHTTP`: net/http calls `ctx.Err()` only from live goroutines (the caller's and the
    transport's own; HTTP/2 after `Done`, and `shouldRetryDial`'s nil test,
    `internal/http2/client_conn_pool.go:284`). Each is a thread, so the read locks held at one time
    on the wrapper's `RWMutex` are bounded by the live threads (`threadBound GF`, 2^28 < 2^30), which
    is what the token accounts for in the logic. In Go the reader counter cannot overflow from them.
  - `Tracer.Start`: `ContextWithSpan(ctx, s)` is a `valueCtx` whose `Err()` is `ctx.Err()` (the
    same call, paid with the same token), or `ctx` itself (the no-op tracer).
- **Review point:** the level choice (4) and that the three trust-boundary texts only use `Err`
  from threads. Callers of the weak context's `Err` in proofs (after the handle work): `watchServer.Watch`
  (after `Done`), `recvLoop` (`watch.go:203`, forked), `leaseKeepAlive` (`lease.go:106,118,149`),
  and the local `WithTimeout` lemma (`propagateCancel`'s `parent.Err()`).
- **Checks:** `SrvCtxWeak.lean` and every module that mentions `srvCtxWeak`
  (`Tracer__Start`, `StartLaws`, `SrvCtxWeakLaws`, `EtcdServer__waitLeader`, `RenewHTTP`) pass
  `etc/lean-check.py -a`; full build (`etc/timed-build.py`, 64G cap, build lock) passes (17492
  jobs); `etc/tcb-report.py --check` matches the baseline unchanged (865 axioms, 5 sorries: the
  statements of the axioms are textually the same); `etc/goose.py --check` passes (with the Goose
  configuration's promoted methods, below). Not run: axiom-tok, collections, gen-interface (none of
  the six API lists exposes these texts; to run with the next gates).
- **Goose configuration** (accepted by etcd-grove-81): `Code/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc.toml`
  lists the wrapper's promoted methods (`cancellableContext.{Deadline,Done,Value}`,
  `serverStreamWithCtx.{RecvMsg,SendMsg}`), regenerated with `etc/goose.py --project etcd`
  (`8227d410c2`).

## Addendum T-g (2026-11-12): the raw stream is a pointer value; `SpanFromContext` reads only `Value` (decided by etcd-grove-81, Q1/Q2)

Found while proving item 7 (the interceptor's insert into the monitor's map; mvcc's `Watch` on the
traced weak context). Both are trusted-text changes; for 81's review with the `axiom` skill at the
mvcc checkpoint, together with the interface diff.

### T-g1 (Q1). `rawStreamKeyTy t` → `rawStreamKey si` (strengthens T-c)

- **Text** (`Proof/google_golang_org/grpc/InvGrpcStream.lean`, `rawStreamKey`; used in
  `srvRawStreamIs`): `∃ (t' : go.GoType) (ls : Loc), si = interface.mk (go.GoType.PointerType t') #ls`
  (was: `∃ t', si.ty = go.GoType.PointerType t'`, the type only). `srvRawStreamIs` says
  `⌜rawStreamKey si⌝`.
- **Why:** the monitor's map key `v3rpc.sKey t ls l` (and `safeMapKey_sKey`, `==` on two keys
  comparing the pointers) needs the raw stream as `interface.mkOk (PointerType t) #ls`; a type
  alone leaves the value an arbitrary `val`.
- **Stronger claim** of grpc's run model (`acceptRun`'s raw end) and of prometheus's contract
  (its handler's raw end).
- **Evidence** (`examples/premisefix/streamctx` `TestRawStreamKey`, extended): at etcd's interceptor
  position and in the handler, with and without grpc-prometheus, the stream is a pointer type
  (`*grpc.serverStream`, `*interceptors.monitoredServerStream`) and the interface's data word
  (`(*[2]unsafe.Pointer)(unsafe.Pointer(&ss))[1]`) is the pointer itself
  (`reflect.ValueOf(ss).UnsafePointer()`): Go stores a pointer-typed dynamic value directly in the
  interface. Passes (`GOWORK=off go test ./premisefix/streamctx -run TestRawStreamKey`). After the
  review (m1): also with otelgrpc's stats handler and through `ServeHTTP` (an HTTP/2 TLS httptest
  server), all eight combinations; `srvRawStreamIs`'s docstring names grpc's one wrapper hook (the
  xDS-internal `xdsFilterWrapperOption`, never set by etcd).

### T-g2 (Q2). `trace.SpanFromContext.spec` and mvcc's `WatchStream.Watch.contract` take `spanCtxOk` only

- **Text:** `Spec/go_opentelemetry_io/otel/trace/SpanFromContext.lean`, pre
  `⌜ctx = trace.todoCtx⌝ ∨ trace.spanCtxOk ctx` (was `⌜…⌝ ∨ (context.isContext ctx cd ∗
  trace.spanCtxOk ctx)`), the binder `cd` kept (unused); `Spec/go_etcd_io/etcd/server/v3/storage/mvcc/Api.lean`
  `WatchStream.Watch.contract`, the context part `⌜ctx = todo⌝ ∨ trace.spanCtxOk ctx` (was with
  `isContext ctx cd`), `cd` kept. **Weaker premises** (the axiom claims more; the sealed API asks
  less: an interface diff of mvcc's API).
- **Why:** etcd's `recvLoop` passes mvcc's `Watch` the traced stream context, a weak one
  (`srvCtxWeak`), not an `isContext`; mvcc's `watchStream.Watch` reads only `SpanFromContext(ctx)`.
- **Faithful:** otel v1.47.0 `trace/context.go` `SpanFromContext` returns `noopSpanInstance` for a
  nil context, else `ctx.Value(currentSpanKey).(Span)` or `noopSpanInstance`: no other method of
  `ctx`. **Evidence:** `TestSpanFromContextValueOnly` (same package): a context whose `Deadline`,
  `Done` and `Err` panic and whose `Value` answers nil or a span: `SpanFromContext` returns the
  no-op span and the span (by its `SpanContext`). Passes.
- Callers repaired: mvcc's `watchStream.Watch` proof (`hspan ctx cd`), `processInternalRaftRequestOnce`
  (unchanged text, checks).

### The T-g review (2026-11-12): READY WITH CHANGES, applied (decided by etcd-grove-81)

- M1: the axiom-tok entry of `RenewHTTP` said net/http never calls the caller's `Err()`; false on
  a context already done (`propagateCancel`/`Cause`, go1.27.3 `context.go:487, 290`). The entry, the
  T-f text above and `RenewHTTP`'s docstring restated; `TestRenewHTTPErrTiming` has the pre-cancelled
  case (two calls, a `*url.Error`). The token argument stands (each call on a live goroutine).
- m1: `TestRawStreamKey` covers the stats handler and `ServeHTTP`; `srvRawStreamIs`'s docstring
  names the xDS-only wrapper hook.
- m2 (kept for cleanup): `SpanFromContext.spec`'s and mvcc's `WatchStream.Watch.contract`'s `cd`
  binder is unused; drop it with its callers (`hspan ctx cd`) in a later pass.
- m3: the `Tracer.Start` axiom-tok entry says `Start` never calls `ctx.Err()` (otel's noop and sdk
  tracers).

### Checks run, Revision 2 (2026-11-12, merged with lean `219ddbbb83`)

Full build passes (17490 jobs); `tcb-report --check` matches the baseline unchanged (865 axioms, 5
sorries: the two field axioms are used by no root yet); 55 collections match; axiom-tok ok (811 walked:
779 pass, 32 by an entry or pair) and its selftest; model-param, errdesc ok; gen-interface `--check` on
the six lists: no diff; `examples/premisefix/{streamctx,tracerspan}` pass at go1.27.3.

### Checks run, Revision 1 (2026-11-12)

- Targeted build of the changed modules, then the full build (`etc/timed-build.py`, 64G cap, under
  the build lock): passes (17487 jobs).
- `etc/tcb-report.py --check`: matches the baseline unchanged (865 axioms, 5 sorries). The two new
  axioms (`metadata.incomingOf_cancelCtx`, `v3rpc.incomingOf_cancellableContext`) are used by no root
  yet; they enter the baseline when the weakening interceptor contract uses them (step 3 of §4).
  The 55 collections match.
- axiom-tok: T-e''s `auth.ctxDoneAny` puts an `∃ s : ContextDesc` (inside `isContextDone`) into
  every axiom holding `isReqAuth`: ten rule-7 findings (`EtcdServer.{adjustTicks, ensureLeadership,
  leaseTimeToLive, monitorClusterVersions, monitorStorageVersion, publishV3, purgeFile,
  waitAppliedIndex, waitLeader}.wp_proof`, `etcd_noRefusal`), accepted by new entries in
  `etc/axiom-tok-allow.txt` (rule 7's neutral case through a handle, as `NewStream`'s `cd'`: `s.PDone`
  only under Perennial's irreducible `isContextDone`, and the auth store's posts mention nothing of
  `s`). **For the review.** With them: ok (811 Prop axioms walked: 779 pass, 32 by an entry or pair); selftest 0 failures.
- model-param, errdesc, errorf-wrap, bounds (331, baseline 331): ok. gen-interface `--check` on the
  six lists: no diff.
- m4, the collections whose baselines include `grpc.model.acceptRun`/`acceptRunConns` and
  prometheus's `ServerMetrics.StreamServerInterceptor` (both): authkv, cachekv, compactkv,
  k8scompactor, k8setcd3, leasecatchup, leaseexpiry, leasekv, linkv3p, linkvtxn, m2, putget, putget3,
  watchkv; prometheus's only: v3rpc. They rest on T-a/T-c's and M1's stronger `srvRawStreamIs`.
- Go: `examples/premisefix/streamctx` at go1.27.3: passes.

### Checks run (2026-11-12, on 783fd4c8c8)

- Full build (`etc/timed-build.py`, under the 64G cap): passes. Two earlier full builds from the
  stale tree were OOM-killed at the cap (aggregate of parallel jobs, `run-…scope: oom-kill`, 64G
  peak); a targeted build of the changed modules' users, then the timed full build, passed.
- `etc/tcb-report.py --check`: **matches the baseline unchanged (865 axioms, 5 sorries)**. The new
  axiom `metadata.incomingOf_of_value` is not yet used by any result, so no root reaches it; it
  enters the baseline (`--check --update`) at step 3, when the wrapper's metadata lemma uses it.
  The 55 collections match. No `--update` was run.
- axiom-tok (and its selftests), model-param, errdesc: ok.
- `etc/gen-interface.py` for the six API lists: no diff (none of them exposes these texts).
- Go: `examples/premisefix/streamctx` passes (the four tests above).

### Coordination (etcd-grove-81's note, 2026-11-12)

The planned auth stage S1 makes the auth token contract's info clause take `auth.ctxDoneAny`
(`Done()` returns nil or a channel safe to receive on). `srvCtxWeak`'s `#HDone` is `isContext`'s, so
it gives that. **Conflict with T-e:** `isReqAuth`'s triples now take only `libCtxOk ctx`, and the
`txnCtx` they drop (`doneNil ∨ isContext`) was the only Done fact there. If S1's `AuthInfoFromCtx`
needs `ctxDoneAny`, `isReqAuth`'s triples must take it back: recommended form `libCtxOk ctx ∗
auth.ctxDoneAny ctx (∗ RD)`, which both `txnCtx` and `srvCtxWeak` give, rather than restoring
`txnCtx` (which a weak handler context does not meet). Either S1 adds it, or T-e is restated so
now if S1's definition is available.

### Not trusted (definitions and proofs only; listed for the review's completeness)

- The two interceptor contracts (R-3): `srvStreamInterceptorOk` (strong in, strong out) is unchanged,
  and prometheus's axiom keeps it (with T-a/T-c's stronger stream end); the new
  `srvStreamInterceptorWOk ic R` (strong in; the handler on a weak end `srvStreamIsW` with
  `⌜incomingOf ci' = incomingOf ci⌝`, or an early `srvErrOk` error) is proved for etcd's
  `newStreamInterceptor`; the chain lemma for `ics ++ [icW]`; `grpcStreamHandlerOk` takes the weak
  end. These are consumed only by proofs (`Results.lean`, `_Watch_Watch_Handler`, the
  registrations' proofs), not by an axiom.
- mvcc's `WatchStream.Watch.contract` (Q-RB4): a proved, sealed API; changed at step 5's checkpoint.
- The deletion of `runsNoRequireLeader` (step 6).
