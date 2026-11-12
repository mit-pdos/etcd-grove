# k8s 7f-4, require-leader streams: re-baseline against lean (2026-11-12, to etcd-grove-81)

The 7f-4 Draft (`notes/k8s-7f4-draft.md`, accepted 2026-11-08 against lean `3a08c2abee`) was to
start Lean after per-type and stage B. Both have landed, and so have premise fixes 7 and 8, the
ctx-value change in Perennial (pin `ddc0f0acc`) and model-param. This note checks the Draft against
lean `6803e4e0fd` (7f-2 landed). No Lean is written.

**Verdict:** not form-only. Three Draft items change in meaning (§2: R-1, R-2, R-3), and two
estimates grow. Stop for 81 before any 7f-4 Lean.

## 1. What changed in lean that 7f-4 touches

| Change (landing) | Where | Effect on the Draft |
| --- | --- | --- |
| Stream handler post: `srvErrOk err ∗ S` (per-type stage B, B1b; premise fixes 7) | `grpcStreamHandlerOk`, `InvGrpcStream.lean:740` | W2, L1: the handler's error is no longer unconstrained. `c.Err()` after `Done` must be `srvErrOk` (§2, R-4) |
| Interceptor contract: `StreamMsgT` with the registries, `srvErrOk` on both continuations; the per-interceptor resource `R` (`True` for etcd's) | `srvStreamInterceptorOk`, `:798`; `srvStreamChainWP_of_ok` | §3's change sits on top. The early `ErrGRPCNoLeader` refusal already proves `srvErrOk` (`error_return eNL with SeNL`, `newStreamInterceptor.lean`) |
| Run contract: `threadTok ∗ £ 1` given and the token returned; `grpcSrvCfg`, `acceptRun`, leveled pools | `InvGrpcRun.lean`, `InvGrpc.lean:892` | None for the branch itself (it forks nothing; `WithCancel(ci)` on grpc's `*valueCtx` over a `*cancelCtx` starts no goroutine). The handlers already return `S` |
| `grpcRunCtx ci` now `etcd keys nil ∗ trace.spanCtxOk ci ∗ context.libCtxOk ci` (premise fixes 7) | `InvGrpc.lean:200`, `Proof/context/LibKeys.lean` | **The stream handlers now use it** (`libCtxOk_of_runCtx` in `LeaseServer__leaseKeepAlive.lean:192`; `spanCtxOk_of_runCtx` in `serverWatchStream__recvLoop.lean:459`). Q7f4-2 no longer holds (R-1) |
| Auth path: `FromIncomingContext`, `AuthInfoFromTLS` take `incomingCtxOk`/`peerCtxOk`; `isReqAuth`'s triples take `txnCtx ∗ libCtxOk` (premise fixes 8 S2) | `InvRequest.lean:2635` | Q7f4-3: T2 is half done. If `isReqAuth`'s realizers no longer use `txnCtx`, it can go and W3/L5 need only `libCtxOk ci'` |
| `LeaseRenew.spec`: `isContext ∗ libCtxOk`, `E.RD`, `lessorRdPool`, `levelTok lessorLvl` | `Spec/.../EtcdServer__LeaseRenew.lean` | L3: the premise becomes `srvCtxWeak ∗ libCtxOk` (the levels stay) |
| `Tracer.Start` gives `spanCtxOk`/`startTimeOk`/`libCtxOk` transfer wands; an **open** note (isSpan not justified for every `txnCtx`) | `Spec/.../traceutil/Tracer__Start.lean` | W4/L4: add `srvCtxWeak ctx -∗ srvCtxWeak ctx'`. The open note is not 7f-4's to fix, but the weak disjunct must not widen it: the contexts passed are still grpc's run contexts' children |
| mvcc's `Watch` contract moved into mvcc's API: `todoCtx ∨ (isContext ∗ spanCtxOk)` | `Spec/.../mvcc/Api.lean:760` (`WatchStream.Watch.contract`) | W5 becomes a change to a **sealed package API** (an interface diff), not just an internal spec |
| Perennial `ctxValue`/`ctxValueFrom` (P-RL1 landed, `ddc0f0acc`); `LibKeysChain.lean` (the chain form of the outgoing fact) | Perennial `Proof/context/CtxValue.lean` | The wrapper's `Value` laws exist (L2 `ctxValue_cancel`, `ctxValue_Value`), but only from a parent's **chain** form (R-1, R-2) |
| `runsNoRequireLeader` | 26 files (unchanged count) | §7's list: regenerate at the deletion step (more closed theorems may reach it since 7e) |

## 2. Draft items that change in meaning

- **R-1. Q7f4-2 (drop `grpcRunCtx` from `srvStreamIs`) is withdrawn.** The handlers use
  `libCtxOk` (LeaseRenew's premise, the auth path) and `spanCtxOk` (mvcc's `Watch`, `Tracer.Start`)
  of the run context. The weak stream end must carry, for the wrapper `ci'`, `libCtxOk ci'` and
  `trace.spanCtxOk ci'` (and the etcd-prefixed-keys fact if a stream path reads it; to enumerate).
  - These do not follow from `grpcRunCtx ci` for `ci' = cancellableContext{WithCancel(ci)}`: Go's
    `value()` walks a `*cancelCtx`'s parent chain without calling the parent's `Value`, so a WP
    fact about `ci.Value` says nothing about the child (`LibKeysChain.lean`'s header).
  - **Proposed:** grpc's model states the run context's library and etcd-key facts also in the
    chain form (`ctxValue ci k R` at the four library keys and the etcd keys; true in Go: grpc's
    run context is a `*valueCtx` chain over a `*cancelCtx`). A change to trusted grpc text, which
    is what the Draft's §8 gap (a) already foresaw. Then `ctxValue_cancel` gives `WithCancel(ci)`,
    and `ctxValue_Value` on the promoted `Value` gives the wrapper's WP facts.
- **R-2. Q7f4-1 (F1's form): F1-general now, in place of F1-narrow.** premise fixes 7 put
  `metadata.incomingCtxOk ci` (`Value(mdIncomingKey{})` returns one value `v` on every call) in the
  run context. So F1-general is statable without the second grpc change the Draft feared:
  `valueAt c mdIncomingKeyAny (· = v) ∗ valueAt c' mdIncomingKeyAny (· = v) ⊢
  ⌜incomingOf c = incomingOf c'⌝` (an axiom on the opaque `incomingOf`; true in Go:
  `FromIncomingContext` reads only `Value(mdIncomingKey{})`, and `transportMD` is never written
  after). It is no more trust than F1-narrow and serves every derived context. With R-1's chain
  form, the wrapper's `valueAt` at the key follows.
- **R-3. §3's contract shape: the interceptor's input keeps grpc's strong context.** The Draft
  weakened `srvRawStreamIs`'s context to `srvCtxWeak` everywhere. But etcd's interceptor calls
  `WithCancel(ss.Context())`, and Perennial's `WithCancel` needs `isContext parent`
  (`isParentCtx`). The chain is `[prometheus, newStreamInterceptor]` (`v3rpc/grpc.go:62`), so etcd's
  interceptor sees prometheus's wrapper, whose context is grpc's `ci`.
  - **Proposed:** `srvRawStreamIs` is parametrized by its context fact: strong (`isContext ∗
    grpcRunCtx`, plus R-1's chain facts) or weak (`srvCtxWeak ∗ libCtxOk ∗ spanCtxOk`). Two
    interceptor contracts: **preserving** (the output stream's context is the input's, any fact:
    prometheus, today's form) and **weakening** (strong in, weak out with F1's equality: etcd's).
    The chain lemma is stated for "preserving then weakening", and `grpcStreamHandlerOk` gets the
    weak end. Still one package of trusted text through the `axiom` skill (with F1, F2, F3 and the
    weakened premises).
- **R-4 (form, listed for review).** `srvCtxWeak`'s `#HErrDone` gives `isCtxErr err ∨
  noLeaderErr err`; the handlers need `srvErrOk err` for their post. Both disjuncts give it
  (a context error through `applyErrIs_srvErrOk`, as `watchServer__Watch.lean:392` does today; `ErrGRPCNoLeader` through its `statusErrOk`, `SeNL` in `newStreamInterceptor.lean`).
  No restatement of the contract, only a lemma.

## 3. Draft items that still hold

- §2's contract (`srvCtxWeak`, `noLeaderErr`, the `isContext → srvCtxWeak` law), with R-4's lemma.
- F2 (`WithRequireLeader` over a caller's context), F3 (the raw stream's dynamic type is a
  comparable key), the `sKey` map-key instance (R1, `notes/k8s-7f4-mapkey-check.lean.txt`; to
  re-check against today's Perennial map specs before use).
- Q7f4-4 (P-RL2 for `WithTimeout` as a local lemma), Q7f4-5 (the three weakened trust-boundary
  premises). Note on Q7f4-4: Perennial's `WithTimeout`/`WithCancel` need `isContext parent`, so the
  local lemma re-proves `propagateCancel` over the wrapper (it answers `Value(&cancelCtxKey)` with
  its inner `*cancelCtx`, so the timer context registers as that one's child). Larger than the
  Draft's estimate.
- §5's table of uses (W1-W7, L1-L7), with the changes of §1 (W2/L1 need R-4; W3/L5 `libCtxOk`;
  W5 is a mvcc API change; L3's premise keeps the levels).
- §6's branch and monitor; R2 (the monitor's wait terminates).

## 4. Revised order and checkpoints

1. **Enumerate** (no Lean): `isReqAuth`'s realizers' use of `txnCtx` (Q7f4-3, now likely T2 by
   deletion); the stream paths' uses of `grpcRunCtx`'s three parts; the `runsNoRequireLeader`
   closed theorems (`etc/importers.py --uses commonPremises --files`, with `etc/tcb-report.py`'s
   roots).
2. **The trusted package** (text only, through the `axiom` skill): R-3's two contracts and the
   parametrized stream end; R-1's chain-form run-context facts; F1-general (R-2); F2; F3; the
   weakened `Tracer.Start`/`waitLeader`/`RenewHTTP` premises. **Hard stop for review.**
3. `srvCtxWeak`, its laws, R-4's lemma; the wrapper's library facts from the chain form.
4. The interceptor branch and the monitor (the `sKey` instance first).
5. Watch's chain (including mvcc's API change, W5: interface diff, **checkpoint**), then
   LeaseKeepAlive's with `LeaseRenew` and the local `WithTimeout` lemma.
6. The deletion of `runsNoRequireLeader`, the interface files, `etc/tcb-report.py --check
   --update`. **Hard stop** (closed theorems' premises change; trust base changes).

Estimate: the Draft's 2850-5150 lines, plus 300-600 for R-1/R-3 (the parametrized stream end, two
contracts and the chain lemma) and 200-400 for the larger `WithTimeout` lemma.

## 5. Questions for 81

- **Q-RB1.** Withdraw Q7f4-2 and adopt R-1 (chain-form run-context facts in grpc's model).
  Recommended: yes.
- **Q-RB2.** Q7f4-1 changes to F1-general now (R-2). Recommended: yes.
- **Q-RB3.** §3 becomes R-3's two contracts with a parametrized stream end. Recommended: yes.
- **Q-RB4.** W5 changes mvcc's sealed API (`WatchStream.Watch.contract`'s context disjunct gains
  the weak form). Recommended: yes, as an API diff reviewed at step 5's checkpoint.
