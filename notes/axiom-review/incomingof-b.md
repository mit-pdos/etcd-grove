# incomingof Part B: the context errors' descriptions — exact texts and soundness note (2026-11-17)

Branch `incomingof-scope`, the incomingof agent of etcd-grove-03. **Approved by the user 2026-11-17 via
etcd-grove-03**: (1) delete `ContextReadErrs`' `Canceled` half (the location-free `DeadlineExceeded` half
stays); (2) `ctxErrsErr`'s conjunct in message form, server per-run facts from `toGRPCErrorMap_init`'s own
conjuncts; (3) the context-error case in the client's Range error outcome (`client_range_any`'s text changes),
which k8s `Get`/`List` rule out; (4) `errors.IsStatusErr.spec` strengthened for an `EtcdError` target. This file
gives every new or changed trusted text exactly, and checks each against (a) `crossWorld`, (b) the
persistent-authoritative-heap fresh world (the attack that refuted Part A, `incomingof.md`), (c) adequacy plus
nondeterministic allocation (Scope §0.2). **Status: awaiting the independent attack. No Lean changed yet.**

## The attack model, stated once

Let `W` be a world built inside the logic at a fresh heap name, owning a persistent authoritative heap
`Auth DFrac.discard σ` for a finite `σ` of the attacker's choice, and any fragments agreeing with it. In `W`:
- every points-to agrees with `σ`, so a wand `l ↦□ v -∗ ⌜P⌝` holds as soon as `P` holds for the `v = σ(l)`;
- **every WP of a non-value holds** (the state interpretation, which owns the full authority, is incompatible
  with the discarded one, so the WP's premise is false). So `errorMsgIs e m` holds for every `e`, `m`;
  likewise `errMsgOk`, `grpcErrMethodsOk`'s WP parts, `ctxErrsErr`, `statusErrOk`'s WP parts;
- no triple's post becomes a Lean fact (adequacy needs a real state interpretation).

So a trusted text is exposed exactly when it is an **entailment** (an axiom `A ⊢ B`, or a premise-class field
`A ⊢ B`, quantified over `hG`) whose `A` holds in some such `W` and whose `B` contains a pure fact that is not
a Lean consequence of what `A` pins down in `W`. A pure fact inside a **triple's post**, or a pure fact a
**continuation receives** (the `Φ` of a WP form), is not exposed to (a)/(b); it is exposed to (c) only if the
code has Lean semantics and the fact depends on an allocated address.

## T1. `ContextReadErrs` (premise class; `Proof/go_etcd_io/etcd/server/v3/etcdserver/read/Init.lean:68-86`)

Old field `descs` (both halves, entailment from `isPkgInit context`):
```lean
  descs : isPkgInit (PROP := IProp GF) pkg_id.context ⊢
    (∃ e : GoInterface, globalAddr _root_.Perennial.context.Canceled ↦□ e ∗
        ⌜go_etcd_io.etcd.cache.v3.errDesc e = go!"context canceled"⌝) ∗
      (∃ d : GoInterface, globalAddr _root_.Perennial.context.DeadlineExceeded ↦□ d ∗
        ⌜go_etcd_io.etcd.cache.v3.errDesc d = go!"context deadline exceeded"⌝)
```
New field (replaces `descs`; pure, no resource):
```lean
  descDeadline : go_etcd_io.etcd.cache.v3.errDesc
      (interface.mkOk _root_.Perennial.context.deadlineExceededError.ty
        #(zero_val _root_.Perennial.context.deadlineExceededError)) = go!"context deadline exceeded"
```
`errs` unchanged.
- (a)/(b): no antecedent, so no world to build; it is one Lean fact about one closed value with no location
  (an empty struct). Nothing transfers.
- (c): not a post. Per run it agrees with the only `errDesc` source on such a value, `status.FromError`'s post
  (its `Error()` is the literal: Perennial `context/NewErrorString.lean:73-78`).
- `errs` (unchanged) re-checked under (b): its conclusion's pure parts are `errLeafW e` (types and method sets
  only), which `isPkgInit context`'s own `isInit` type facts (`Canceled` a `*errorString`, `DeadlineExceeded`
  `deadlineExceededError{}`) determine, so `W` must satisfy them too; its other parts are WP forms.
- Note: after Part B, `descDeadline` may have no user (the producers below use `errorMsgIs`, not `errDesc`). If
  so I will propose deleting it at the land stop (a premise removed only weakens the closed theorems).

## T2. `ctxErrsErr` and the client's `ctxErrClient` (`grpc/InvGrpc.lean:1419`, `client/v3/InvKVConn.lean:1590`)

Both bodies (identical, `ctxErrClient_eq_errs`); old continuation conjunct:
```lean
        ⌜err = interface.nil ∨ go_etcd_io.etcd.cache.v3.errDesc err ∉ handlerDescs⌝ -∗ Φ #err) -∗
```
New:
```lean
        (⌜err = interface.nil⌝ ∨ ∃ (e : GoInterfaceOk) (m : GoString),
          ⌜err = GoInterface.ok e ∧ m ∉ handlerDescs ∧ go_etcd_io.etcd.cache.v3.ctxErrShape e⌝ ∗
          go_etcd_io.etcd.cache.v3.errorMsgIs e m) -∗ Φ #err) -∗
```
with, new in `Proof/go_etcd_io/etcd/cache/v3/Base.lean` (pure, about types only):
```lean
/-- A context error's shape: not an `rpctypes.EtcdError` and without an `Is(error) bool` method (Go's
`Canceled`, a `*errors.errorString`, and `DeadlineExceeded`, a `deadlineExceededError`). -/
def ctxErrShape (e : GoInterfaceOk) : Prop :=
  e.ty ≠ go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty ∧
    methodSet e.ty !! go!"Is" ≠ some (go.Signature [go.error] false [go.bool])
```
Docstring sentence: `Err()`'s non-nil error stably returns from `Error()` some message `m` that is no handler's
description (`errorMsgIs e m`, `m ∉ handlerDescs`), and is not an `EtcdError` and has no `Is` method; grpc's
invoker on a done context returns `status.FromContextError(ctx.Err())`, which keeps `m` as the status message.
- (a)/(b): `ctxErrsErr` is a definition (a WP form), not an entailment. In `W` it holds for every context
  (WP forms do), which is harmless: no trusted text has `ctxErrsErr`/`ctxErrClient`/`ctxOk` as the antecedent of
  an entailment (checked: no axiom or premise field with these, `statusErrOk`, `errorMsgIs` or `errMsgOk`
  left of `⊢`). Its pure facts (`m ∉ handlerDescs`, `ctxErrShape e`) are given to the continuation `Φ`, i.e.
  per call. Unlike the old conjunct there is no pure `errDesc` fact of a pointer at all.
- (c): `ctxErrsErr` is not a post; its producers prove it per run (below) from `context.isInit`'s cell
  `x.s ↦□ "context canceled"` with `errorString.Error`'s proved WP (Perennial `wp_isCtxErr_Error`), and from
  the types (`go.method_set_is` for `*errors.errorString` and `context.deadlineExceededError`, as
  `errorStringNoGRPCStatus_inst` does). Its consumers: (i) grpc's invoker model `grpcInvokerOk` (trusted,
  unchanged), whose post grants `Ψe (errDesc err)` only at `handlerDescs` descriptions: Go meets it because
  `FromContextError` keeps `m ∉ handlerDescs` (Go below); (ii) `ContextError`'s proof (T5); (iii)
  `waitRetryBackoff.spec` (an axiom over a names-only function, text unchanged: its post's `errDesc err ∉
  handlerDescs` is the `status.Error` of `ctx.Err().Error()`, which is now exactly what the message form says
  in Go terms; a post of uninterpreted code, so not exposed to (a)-(c)).

## T3. `errors.IsStatusErr.spec` (trusted spec; `Spec/errors/IsStatusErr.lean:46`)

Old post:
```lean
  {{ (b : Bool), RET #b; ⌜b = true → errDesc err = errDesc target⌝ }}
```
New post:
```lean
  {{ (b : Bool), RET #b; ⌜b = true → errDesc err = errDesc target ∧
      ((∃ x : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError,
          target = interface.mkOk go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty #x) →
        ∀ e : GoInterfaceOk, err = GoInterface.ok e →
          methodSet e.ty !! go!"Is" ≠ some (go.Signature [go.error] false [go.bool]) →
          e.ty = go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)⌝ }}
```
**Deviation from the approved wording, needed for truth:** the user's form "for an `EtcdError` target, `b = true
→ err.ty = EtcdError.ty`" is false for a leaf error with an `Is` method, which `statusErrOk` allows
(`grpcErrMethodsOk` only requires `Is` to answer `true` for a target of the same description): Go
`TestIsEtcdTarget`, `*descIs` with the future-revision text, `errors.Is(…, EtcdError) = true`. So the type
conclusion is guarded by "no `Is` method". The k8s consumer needs nothing more: context errors have no `Is`
method (`ctxErrShape`).
- Why true in Go: `errors.Is(err, target)` on a leaf error (`statusErrOk`: no `Unwrap`) is `(comparable(target)
  && err == target) || (err has Is(error) bool && err.Is(target))` (go1.27.3 `src/errors/wrap.go`, `is`); with no
  `Is` method only `err == target` can answer `true`, and interface equality compares dynamic types first.
- (a)/(b): a triple's post, not an entailment; in `W` the triple is vacuous and exports nothing.
- (c): `errors.Is` is Perennial code with Lean semantics, so adequacy turns the post of a closed program's call
  into a Lean fact about that run. The new conjunct is about the dynamic type of the argument and its method
  set: no address enters it, so nondeterministic allocation cannot vary it, and in Lean's semantics of
  `errors.Is` `==` on interfaces compares types. (The *existing* conjunct `errDesc err = errDesc target` is a
  pure `errDesc` fact over interpreted code, exposed to (c) as Scope §0.2 says of every such post; not changed
  here, and listed for the per-heap Scope.)

## T4. The client's Range error outcome (exported `client_range_any`, `client/v3/Results.lean:2865`)

`client_range_any`'s statement names `rangeErrOut` (`client/v3/KVService.lean:1021`); its text changes through
that definition. Old:
```lean
def rangeErrOut (ms : List (SrvAt GF)) (c : w64) (F : mvcc.Log) (o : OpFull)
    (Q : KVState → IProp GF) (err : GoInterface) : IProp GF :=
  iprop(⌜err ≠ GoInterface.nil ∧ ∀ x ∈ ms, noRefusalAt x.addr⌝ →
    rangeErrΨ ms c F o Q (go_etcd_io.etcd.cache.v3.errDesc err))
```
New:
```lean
def rangeErrOut (ms : List (SrvAt GF)) (c : w64) (F : mvcc.Log) (o : OpFull)
    (Q : KVState → IProp GF) (err : GoInterface) : IProp GF :=
  iprop(⌜err ≠ GoInterface.nil ∧ ∀ x ∈ ms, noRefusalAt x.addr⌝ →
    (rangeErrΨ ms c F o Q (go_etcd_io.etcd.cache.v3.errDesc err) ∨
      ⌜∃ e : GoInterfaceOk, err = GoInterface.ok e ∧ go_etcd_io.etcd.cache.v3.ctxErrShape e⌝))
```
Read: a failed range's error has the outcome at its description, or is the context's error (which `ContextError`
returns as it is: fork `client/v3/client.go`, `ContextError`'s `DeadlineExceeded`/`Canceled` branch).
Not trusted (a definition in an exported statement; proved). Location-free disjunct (types).

The internal chain changes with it (not trusted, proved; listed for review):
- `ContextError.spec` (`Spec/go_etcd_io/etcd/client/v3/ContextError.lean:44`), last conjunct, old
  `⌜err ≠ nil → errDesc err' = errDesc err ∨ errDesc err' ∉ handlerDescs⌝`, new
  `⌜err ≠ GoInterface.nil → errDesc err' = errDesc err ∨ ∃ e, err' = GoInterface.ok e ∧ ctxErrShape e⌝`.
- `kv.Do.specG` (`client/v3/KVMembers.lean:201`): `ifcErrOut … Ψr err` becomes `ifcErrOut … Ψr err ∨ ⌜∃ e, err =
  GoInterface.ok e ∧ ctxErrShape e⌝`; `ifcErrOut_desc` takes the first disjunct only.
- `kv.Get`'s proof (`kv__Get.lean:123`): the new disjunct to `rangeErrOut`'s.

## T5. k8s rules it out (`client/v3/kubernetes/Defs.lean:311`, `k8s apiserver etcd3/ListDefs.lean:369`)

Both premises gain the type condition `errors.Is` gives (not trusted; proved; the same edit in both):
```lean
def rangeErrSound (o : w64) (Q : w64 → KVState → IProp GF) (err : GoInterface) : IProp GF :=
  iprop(□ (⌜go_etcd_io.etcd.cache.v3.errDesc err = go_etcd_io.etcd.cache.v3.futureRevDesc⌝ -∗
      ⌜∀ e : GoInterfaceOk, err = GoInterface.ok e →
        methodSet e.ty !! go!"Is" ≠ some (go.Signature [go.error] false [go.bool]) →
        e.ty = go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty⌝ -∗
      ∃ (R : w64) (σ : KVState), □ Q R σ ∗ ⌜σ.rev < sint.nat o⌝))
```
(`readErrIs`'s second conjunct the same.) `Client.Get`/`List` prove it from `rangeErrOut`: in the context case,
`ctxErrShape e` says no `Is` method and `e.ty ≠ EtcdError.ty`, contradicting the premise. `store.listReadError`
discharges both premises from T3's post (`errors.Is(err, ErrFutureRev)`, an `EtcdError` target by
`rpctypesInit`). No closed statement names `rangeErrSound`, `readErrIs`, `rangeErrOut` (checked: only proofs
and the `Spec` files of `Client.Get`/`List`/`getList`/`listReadError`).

## T6. The server's per-run facts (`v3rpc/Base.lean:230`, `ctxErrDescs`; not trusted)

Old: the two `errDesc` equations from `descs`. New, only what its one consumer (`ServerKVOn.lean:802-826`,
`rangeErrOther_facts`) needs:
```lean
def ctxErrDescs : IProp GF :=
  iprop((∃ e : GoInterface, globalAddr _root_.Perennial.context.Canceled ↦□ e ∗
      ⌜go_etcd_io.etcd.cache.v3.errDesc e ≠ go_etcd_io.etcd.cache.v3.futureRevDesc ∧
        go_etcd_io.etcd.cache.v3.errDesc e ≠ go_etcd_io.etcd.cache.v3.compactedDesc⌝) ∗
    (∃ d : GoInterface, globalAddr _root_.Perennial.context.DeadlineExceeded ↦□ d ∗
      ⌜go_etcd_io.etcd.cache.v3.errDesc d ≠ go_etcd_io.etcd.cache.v3.futureRevDesc ∧
        go_etcd_io.etcd.cache.v3.errDesc d ≠ go_etcd_io.etcd.cache.v3.compactedDesc⌝))
```
Proved in v3rpc's `initialize'` (`Init.lean:296`) from the post of the trusted `toGRPCErrorMap_init` (unchanged):
its wand `□ ∀ g k, g ∈ grpcErrKeyGlobals → globalAddr g ↦□ k -∗ ⌜(M !! k).isSome⌝` at `Canceled`,
`DeadlineExceeded` (both in `grpcErrKeyGlobals`, `Base.lean:118-119`), then `grpcErrMapOk`'s
`errDesc k ≠ futureRevDesc ∧ errDesc k ≠ compactedDesc` for the keys of `M`.
- (a)/(b): `ctxErrDescs` is a conjunct of `v3rpcInit`, made only by v3rpc's `initialize'` from that post (a
  triple of the uninterpreted `toGRPCErrorMap.init`). In `W` one could build `ctxErrDescs` by choosing a cell
  value whose `errDesc` is known (e.g. `deadlineExceededError{}`, by T1) — but then its pure facts are true of
  that value, and nothing transfers: the check is that **no trusted entailment takes `isPkgInit v3rpc` (or
  `ctxErrDescs`) as its antecedent**. The four entailments with `isPkgInit v3rpc ⊢` (`SrvCtxWeakLaws.lean:96`,
  `ServerKVOn.lean:996`, `InvKV.lean:486, 503`) are proved lemmas, not axioms or premises.
- (c): the source post is of uninterpreted code; no closed program reaches it.
- The trusted wand in `toGRPCErrorMap_init`'s post (heap cell to pure fact) is in a post of uninterpreted code,
  consumed only by proofs: not exposed. Flagged for the per-heap Scope (same shape as Part A's `incomingKept`,
  safe here only because no entailment consumes it).

## T7. Producers (proved; no trusted text)

`client/v3/ErrorsNewOk.lean:254-306` (`ctxErrClientAllW_of`), `client/v3/ChanCtx.lean:166-219` (`chanCtx_ok`), and
the server producers of `ctxErrsErr` (`TimeoutCtx.lean`, `InvClientNewResult.lean`, `InvClientAuth.lean`,
`InvGrpc.lean`, k8s `compactor__run*Loop`, examples `auth`/`auth3`/`authN`): `Canceled` gives `errorMsgIs e
"context canceled"` from `isInit`'s `x.s ↦□ "context canceled"` and `errorString.Error`'s WP;
`DeadlineExceeded` gives `"context deadline exceeded"` from its `Error` body; `ctxErrShape` from the two types'
method sets. Neither uses `descs`.

## Go evidence

`examples/axiomcx/incomingof/` (own module, grpc v1.84.0), `GOTOOLCHAIN=go1.27.3 GOWORK=off go test -v ./...`,
2026-11-17, all pass:
```
    is_test.go:45: errors.Is(incomingoftest.etcdError "etcdserver: mvcc: required revision is a future revision", EtcdError) = true
    is_test.go:45: errors.Is(*errors.errorString "context canceled", EtcdError) = false
    is_test.go:45: errors.Is(context.deadlineExceededError "context deadline exceeded", EtcdError) = false
    is_test.go:45: errors.Is(*errors.errorString "etcdserver: mvcc: required revision is a future revision", EtcdError) = false
    is_test.go:45: errors.Is(*incomingoftest.descIs "etcdserver: mvcc: required revision is a future revision", EtcdError) = true
--- PASS: TestIsEtcdTarget (0.00s)
    is_test.go:59: *errors.errorString: Error() = "context canceled", "context canceled"
    is_test.go:59: context.deadlineExceededError: Error() = "context deadline exceeded", "context deadline exceeded"
--- PASS: TestCtxErrMessages (0.00s)
    md_test.go:73: *errors.errorString "context canceled": FromError ok=false code=Unknown msg="context canceled"
    md_test.go:73: context.deadlineExceededError "context deadline exceeded": FromError ok=false code=Unknown msg="context deadline exceeded"
    md_test.go:80: FromContextError(Canceled): code=Canceled msg="context canceled"
--- PASS: TestCtxErrDescs (0.00s)
    md_test.go:91: *errors.errorString "context canceled" / *errors.errorString "etcdserver: mvcc: required revision is a future revision"
--- PASS: TestErrorStringDescByCell (0.00s)
```
`etcdError` mirrors `rpctypes.EtcdError`'s shape (a comparable struct, value-receiver `Error`, no `Is`); `errors.Is`
depends only on that. `TestErrorStringDescByCell` is why no pure `errDesc` fact of `Canceled` is stated.

## Trust-base delta (expected)

- Axioms: none added or removed (`incomingOf_cancelCtx` stays: Part A is not linked).
- Trusted texts changed: `ContextReadErrs` (field `descs` → `descDeadline`), `ctxErrsErr`/`ctxErrClient`
  (conjunct), `errors.IsStatusErr.spec` (post). Unchanged but re-justified: `waitRetryBackoff.spec`,
  `grpcInvokerOk`.
- Exported statement text changed: `client_range_any` (through `rangeErrOut`). Closed statements: none (the 50
  closed theorems' `Hctx : ContextReadErrs` keeps its text, with one field fewer).
