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
pins with GOWORK=off, go1.27.1 locally), and what the review should check. T-d (F2) is deferred to
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

### T-b. F1-general: the incoming metadata is a function of `Value(mdIncomingKey{})` (R-2)

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

### T-e'. `isReqAuth` takes the context's `Done()` fact (decided by etcd-grove-81, 2026-11-12; DRAFT, not built)

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
  never call `Err()`; the cancelled call returns a `*url.Error` of `context.Canceled`.
- **Review point (from the previous agent):** net/http's `Err()` vs `Done`: above. Remaining: the
  post `applyErrIs err` for a `*url.Error` wrapping `ErrGRPCNoLeader` (reachable only if the
  derived context took the parent's `Err()` through propagateCancel's goroutine path, which a
  wrapper whose `Value(&cancelCtxKey)` is its inner `*cancelCtx` does not take); the old text
  already claims `applyErrIs` of every `*url.Error` the client returns. The `srvCtxWeak` form
  decision above.

### Checks run (2026-11-12, on this commit)

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
