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

## 2. The trusted package (step 2): text

Each item says where it goes, what it says, and why it is true in Go. "Stronger post" = an axiom
gives more; "weaker pre" = an axiom asks less. All go through the `axiom` skill in 81's review.

### T-a. The raw stream end carries the run context's library facts in the chain form (R-1)

`srvRawStreamIs` (`Proof/google_golang_org/grpc/InvGrpcStream.lean:387`, given by `acceptRun`'s stream
arm through `grpcAccepted`, and by grpc-prometheus's interceptor contract) gains, after
`context.isContext ci cd ∗ grpcRunCtx ci`, the conjunct `context.libCtxOkC ci ∗ trace.spanCtxOkC ci`.
The unary path (`grpcAccepted`'s unary arm, `grpcRunCtx`) is untouched. New vocabulary
(`Proof/context/LibKeysChain.lean`, beside `outgoingCtxOkC`):

```lean
/-- `ctx`'s library values, as Perennial's chain says (persistent): `libCtxOk`'s four facts with
`context.value`'s chain (`ctxValue`) in place of the WP form, so that `WithCancel` and the deadline
constructors carry them (`ctxValueFrom`). -/
def context.libCtxOkC (ctx : GoInterfaceOk) : IProp GF :=
  iprop((∃ v, ⌜metadata.incomingRes v⌝ ∗ ctxValue ctx metadata.mdIncomingKeyAny (· = v)) ∗
    metadata.outgoingCtxOkC ctx ∗ ctxValue ctx peer.peerKeyAny peer.peerRes)

/-- `ctx`'s span is a span, in the chain form (persistent). -/
def trace.spanCtxOkC (ctx : GoInterfaceOk) : IProp GF :=
  iprop(∃ R : GoInterface → Prop,
    □ (∀ v, ⌜R v⌝ -∗ (⌜v = GoInterface.nil⌝ ∨ trace.isSpan v)) ∗ ctxValue ctx trace.spanKeyVal R)
```

(`libCtxOkC` leaves otel's key to `spanCtxOkC`: `libCtxOk`'s `spanValOk` uses `trace.spanRes`, whose
`otelSpan → isSpan` has no law; the handlers need `spanCtxOk`, and the run context's `spanValOk` stays
in `grpcRunCtx`.)

- **Stronger post** of `acceptRun` (stream arm) and of `grpc_prometheus.ServerMetrics.
  StreamServerInterceptor` (its handler's `st'` must carry the same facts: same `ci`, so they are
  the input's).
- **True in Go:** grpc's run context is built by `context.WithValue` links (`metadata.
  NewIncomingContext`, `peer.NewContext`, grpc's internal keys, otelgrpc's `ContextWithSpan`) over the
  transport's `context.WithCancel` of the server's base context; `context.value()` walks exactly
  these links (`*valueCtx`, `*cancelCtx`, `*timerCtx`, `backgroundCtx`), so the chain answers each key
  as the WP form does. To check in review: no link of another type in grpc v1.84.0's server path
  (`http2_server.go` `operateHeaders`, `server.go` `handleStream`/`processStreamingRPC`, otelgrpc's
  `TagRPC`); a link of another type is still covered if it is not one `value()` special-cases
  (`ctxValue_other`).
- **Laws** (proved, step 3): `libCtxOkC ci ∗ ctxValueFrom ci c ⊢ libCtxOkC c` (keys not `*int`:
  `libKeys_notIntPtr`); `isPkgInit context ∗ libCtxOkC c ⊢ libCtxOk c` minus otel's key (+
  `spanCtxOkC` for it); the same two for `spanCtxOkC`.

### T-b. F1-general: the incoming metadata is a function of `Value(mdIncomingKey{})` (R-2)

New axiom (`Proof/google_golang_org/grpc/metadata/Incoming.lean`, beside the opaque `incomingOf`):

```lean
/-- (TRUSTED) `metadata.FromIncomingContext(ctx)` reads only `ctx.Value(mdIncomingKey{})`
(grpc v1.84.0 `metadata/metadata.go`), and the `MD` stored there is never written after
(`transportMD`): two contexts whose `Value` at that key returns the same value on every call have the
same incoming metadata. -/
axiom metadata.incomingOf_of_value (c c' : GoInterfaceOk) (v : GoInterface) :
    context.valueAt (GF := GF) c metadata.mdIncomingKeyAny (· = v) ∗
      context.valueAt c' metadata.mdIncomingKeyAny (· = v) ⊢
    ⌜metadata.incomingOf (GoInterface.ok c) = metadata.incomingOf (GoInterface.ok c')⌝
```

To check in review: `incomingOf` is opaque and indexes the stream `Spec`; the axiom must not let a
proof equate the metadata of contexts whose values differ (it only concludes from equal values).
A value that is not an `MD` (`incomingRes`'s first disjunct): `FromIncomingContext` returns
`(nil, false)` for both, so `incomingOf` agrees (`none`).

### T-c. F3: the raw stream is a comparable map key (Draft §6 R1)

`srvRawStreamIs`'s `∃ si, st = GoInterface.ok si` gains `⌜rawStreamKeyTy si.ty⌝`, where
`rawStreamKeyTy t` (new, `InvGrpcStream.lean`) is: `t` is a pointer type, or a named struct type all of
whose fields are interfaces or pointers (grpc-prometheus's `monitoredServerStream`; checked against
its translation). **Stronger post** of `acceptRun` (grpc-go passes `*serverStream`) and of
prometheus's contract (its `st'` is `&monitoredServerStream{...}` or the struct: to check against
`go-grpc-middleware/providers/prometheus` at the pin). The local `SafeMapKey` instance of the
mapkey check (`notes/k8s-7f4-mapkey-check.lean.txt`) consumes it.

### T-d. F2: `clientv3.WithRequireLeader` over a caller's context

As the Draft §4 (`Spec/go_etcd_io/etcd/client/v3/WithRequireLeader.lean`, a new `spec'` beside the
`Background()` one, which becomes a corollary). Consumer: 7f-3/7f-5a (the store's `watchContext`);
written now so the package is one review, or deferred to 7f-3 if 81 prefers (recommended: defer;
7f-4's server half does not use it).

### T-e. `NewAuthStore`'s request side without `txnCtx` (§1a)

`isReqAuth`'s two triples and `isReqAuthBound`'s take `context.libCtxOk ctx (∗ RD)` only. **Stronger
post** of `auth.NewAuthStore` (axiom). Go: the store's `AuthInfoFromCtx`/`AuthInfoFromTLS` never call
`Done`/`Err` (fork `673da07c8f` `server/auth/store.go`, `AuthInfoFromCtx`, `AuthInfoFromTLS`).

### T-f. The weak handler context and the three weakened trust-boundary premises (Draft §2, §4)

Vocabulary (new, `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/` or a grpc-side module the
specs below can import; `srvCtxWeak`, `noLeaderErr` as the Draft §2, with `#HErrDone` giving
`isCtxErr err ∨ noLeaderErr err`).

- `traceutil.Tracer.Start.spec`: pre `mvcc.txnCtx ctx cd ∨ srvCtxWeak ctx cd`; post adds
  `□ (srvCtxWeak ctx cd -∗ srvCtxWeak ctx' cd)` (otel's `ContextWithSpan` is a `WithValue`, so
  `Done`/`Err` are `ctx`'s; the no-op tracer may return `ctx` itself). **Weaker pre, stronger post.**
  The open note of that spec (isSpan for every `txnCtx`) is not widened: `srvCtxWeak` contexts here
  carry `spanCtxOk`.
- `EtcdServer.waitLeader.spec` (axiom): pre `srvCtxWeak ctx cd` in place of `isContext ctx cd`
  (it selects on `ctx.Done()` only). **Weaker pre.**
- `leasehttp.RenewHTTP.spec` (axiom): pre `srvCtxWeak ctx cd` in place of `isContext ctx cd`
  (`req.WithContext(ctx)`; net/http uses `Done`/`Err`). **Weaker pre.** To check in review: whether
  net/http's transport reads `ctx.Err()` before `Done` and acts on a non-context error (the
  Err-before-Done window, `issues/etcd-stream-interceptor-err-before-done.md`).

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
