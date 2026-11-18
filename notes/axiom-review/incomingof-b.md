# incomingof Part B: the context errors' descriptions — exact texts and soundness note (2026-11-17)

Branch `incomingof-scope`, the incomingof agent of etcd-grove-03. **Approved by the user 2026-11-17 via
etcd-grove-03**: (1) delete `ContextReadErrs`' `Canceled` half (the location-free `DeadlineExceeded` half
stays); (2) `ctxErrsErr`'s conjunct in message form, server per-run facts from `toGRPCErrorMap_init`'s own
conjuncts; (3) the context-error case in the client's Range error outcome (`client_range_any`'s text changes),
which k8s `Get`/`List` rule out; (4) `errors.IsStatusErr.spec` strengthened for an `EtcdError` target. This file
gives every new or changed trusted text exactly, and checks each against (a) `crossWorld`, (b) the
persistent-authoritative-heap fresh world (the attack that refuted Part A, `incomingof.md`), (c) adequacy plus
nondeterministic allocation (Scope §0.2). **Status: the independent attack (etcd-grove-03, 2026-11-17) found no
BLOCKER or MAJOR: all texts survive; its MINORs M1-M5 are folded in below (section "After the attack").**

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
invoker on a done context returns `status.FromContextError(ctx.Err())`, which keeps `m` as the status message,
or prefixes it for an error other than the two context errors (`transport.ContextErr`: `"Unexpected error from
context packet: " + m`), a description that is no handler's either.
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
  `FromContextError` keeps `m ∉ handlerDescs` (Go below); (ii) `ContextError`'s proof (T4); (iii)
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

## After the attack (etcd-grove-03, 2026-11-17): all texts survive; MINORs folded

Go evidence of the attack, with the real `rpctypes` and `ContextError` at the etcd pin:
`examples/axiomcx/incomingof-real/real_test.go` (own module, the fork at the pin as `examples/go.mod` replaces
it; `GOTOOLCHAIN=go1.27.3 GOWORK=off go test -v ./...`, all pass): `TestRealTypes` (`ErrFutureRev` is an
`EtcdError` with methods `{Code, Error}`; `Canceled`, `DeadlineExceeded` have no `Is` and are no `EtcdError`;
`errors.Is` against `ErrFutureRev` is true of an equal `EtcdError`, of non-leaf wrappers, false of a
`*status.Error` of the same description) and `TestContextErrorRaw` (`ContextError` returns the raw
`ctx.Err()` for a gRPC `Canceled`/`DeadlineExceeded` on a done context, a `*status.Error` on a live one).

- **M1. More trusted texts that now claim the message form.** `withVersion.wp_proof` and `tracing.Start.wp_proof`
  (axioms) produce `ctxOk`/`ctxErrClient` of the derived contexts they return, so through `ctxErrClient`'s
  new body they now claim `Err()`'s message form and `ctxErrShape`: true, since a value context's `Err()` is
  its parent's (`context.go`, `valueCtx` embeds its parent; otel's `ContextWithSpan` is a `WithValue`), and the
  parent's satisfies it. `grpc.ClientConn.NewStream.wp_proof` takes `ctxErrClient` in its precondition only,
  so it is weakened (its callers give a stronger fact than before, as the text is a WP form). Texts unchanged.
- **M2.** The `ctxErrsErr` docstring says grpc keeps `m` or prefixes it (done above, T2).
- **M3.** `descDeadline`: deleted if unused after the build (reported at the land stop).
- **M4. `toGRPCErrorMap_init`'s precondition** (`{{ True }}`) could be hardened to
  `[∗ list] g ∈ grpcErrKeyGlobals, ∃ k, globalAddr g ↦□ k`, so that its wand from cells to `(M !! k).isSome`
  speaks only of the cells that exist at the call. Not done: its one caller (v3rpc's `initialize'`) would
  have to collect the 53 keys' persistent points-tos from eight packages' initializers, not cheap. Recorded
  as a pre-existing hardening item for the per-heap Scope; the trusted text is unchanged (old = new).
- **M5.** The T2 → T4 cross-reference is fixed.

## Blocker found while implementing (2026-11-18)

Go's client applies `ContextError` twice on a Range error: `kv.Do` returns `ContextError(ctx, err)` and `kv.Get`
returns `ContextError(ctx, err')` of `kv.Do`'s result (`kv__Do.lean:120`, `kv__Get.lean:73`). T4's
`ContextError.spec` post, `errDesc err'' = errDesc err' ∨ ctx-shaped err''`, keeps a ctx-shaped `err'` only in
its second disjunct: in the first (the description kept, `rpctypes.Error`'s branch) nothing says `err''` is
ctx-shaped, and its description is that of the context error, about which no pure fact exists (the point of
Part B). So `kv.Get` cannot produce `rangeErrOut`'s new disjunct. In Go the second call returns the context
error unchanged (`rpctypes.Error` maps by `ErrorDesc(err) = err.Error()`, `"context canceled"`/`"context deadline
exceeded"`, which no `errStringToError` key is; `errors.As` to `EtcdError` fails; `status.FromError` is not ok).

Options:
- (a, recommended) `ContextError.spec` gains "a ctx-shaped `err` comes back ctx-shaped" (proved spec, stronger
  post), from (i) `ctxErrsErr`'s message restricted to Go's two context messages (`m = "context canceled" ∨ m =
  "context deadline exceeded"`, instead of `m ∉ handlerDescs`; true of every producer) and (ii)
  `rpctypes.Error.spec` strengthened (proved): an error without `GRPCStatus` whose `Error()` stably returns a
  message that is no key of `errStringToError` comes back unchanged (its proof reads `ErrorDesc` as `Error()`).
  The ctx disjunct then carries `errorMsgIs e m` with that `m`. Trusted-text change: (i) narrows T2's
  conjunct (stronger claim on contexts, still true in Go). Estimate 100-200 lines.
- (b) Make the second `ContextError` irrelevant to the outcome: `kv.Get.specG`'s outcome stated of `kv.Do`'s
  error and `kv.Get` returning `ContextError` of it — changes `client_range_any` to speak of an intermediate
  error, not the returned one; rejected (the caller sees only the returned error).

## Option (a), decided by etcd-grove-03 (2026-11-18): the narrowed T2 and the two proved specs

Decided: (1) narrow T2's conjunct from `m ∉ handlerDescs` to Go's two context messages (trusted text claiming
more; true of Go's `context` package at go1.27.3); (2) strengthen the **proved** `rpctypes.Error.spec`: an
error with no `GRPCStatus` method whose `Error()` stably returns a message that is no key of
`errStringToError` comes back unchanged; (3) `ContextError.spec` (proved): a context error comes back as a
context error. M4 stays a pre-existing hardening item (accepted). **Status: the attack on T2' (etcd-grove-03,
2026-11-18) SURVIVES, incl. the planned (2)/(3) (the real `errStringToError` at the pin has 57 keys, neither
context message among them; no other path changes a context error); its MINORs M1-M3 are folded in below
("After the attack on T2'"). Implemented after that.**

### T2' (replaces T2's new conjunct; `grpc/InvGrpc.lean` `ctxErrsErr`, `client/v3/InvKVConn.lean` `ctxErrClient`)

T2's conjunct (as in the WIP head):
```lean
        (⌜err = interface.nil⌝ ∨ ∃ (e : GoInterfaceOk) (m : GoString),
          ⌜err = GoInterface.ok e ∧ m ∉ handlerDescs ∧ go_etcd_io.etcd.cache.v3.ctxErrShape e⌝ ∗
          go_etcd_io.etcd.cache.v3.errorMsgIs e m) -∗ Φ #err) -∗
```
New:
```lean
        (⌜err = interface.nil⌝ ∨ ∃ (e : GoInterfaceOk) (m : GoString),
          ⌜err = GoInterface.ok e ∧ go_etcd_io.etcd.cache.v3.ctxErrMsg m ∧
            go_etcd_io.etcd.cache.v3.ctxErrShape e⌝ ∗
          go_etcd_io.etcd.cache.v3.errorMsgIs e m) -∗ Φ #err) -∗
```
with, new in `cache/v3/Base.lean` beside `ctxErrShape` (pure, a closed list of two literals):
```lean
/-- Go's two context-error messages (`context.go`: `Canceled = errors.New("context canceled")`,
`deadlineExceededError.Error()` returns `"context deadline exceeded"`). -/
def ctxErrMsg (m : GoString) : Prop :=
  m = go!"context canceled" ∨ m = go!"context deadline exceeded"
```
and a proved lemma `ctxErrMsg_not_handler : ctxErrMsg m → m ∉ handlerDescs` (by `decide` on the literals), so
every consumer of the old conjunct keeps working. Docstring: "whose `Error()` stably returns one of Go's two
context messages (`ctxErrMsg`: `Err()` returns only `Canceled` or `DeadlineExceeded`, Go's documented contract)".

**What it claims, in Go.** A context `ctx` satisfying `ctxErrsErr`: once `ctx.Err()` is non-nil, its dynamic
value's `Error()` returns `"context canceled"` or `"context deadline exceeded"` on every call. Go's documented
contract of `Context.Err` ("If Done is closed, Err returns a non-nil error explaining why: DeadlineExceeded if
the context's deadline passed, or Canceled if the context was canceled for some other reason") says exactly
which two errors; their messages are fixed (`Canceled`'s `s` field is never written; `deadlineExceededError`'s
`Error` returns a literal).

**Who makes it (every producer; none can produce a third message).**
- Proved, over Perennial's context model: `ctxErrClientAllW_of` (`client/v3/ErrorsNewOk.lean`, every
  `isContext`; the other files of T7's list pass it or `ctxErrClientAllW` on, or use InvGrpc's lemmas over it), from `context.ErrAny.spec` (`Spec/context/ErrAny.lean`,
  the existing trust boundary, unchanged), whose post already says the error **is** the value of `Canceled`
  (an `*errorString` whose `s` cell is `↦□ "context canceled"`) or of `DeadlineExceeded` (whose `isInit` value is
  `deadlineExceededError{}`, `Error` translated). So T2' adds no claim beyond `ErrAny`'s for these.
- Proved, over the translated k8s `channelContext` (`client/v3/ChanCtx.lean`, `chanCtx_ok`): `Err()` returns
  the value of `context.Canceled` (k8s `wait.go`).
- Trusted, by transfer only: `withVersion.wp_proof` and `tracing.Start.wp_proof` (axioms) take `ctxOk`
  (`tracing.Start` also `ctxErrClient`) of the parent and give the same of the derived context: a `valueCtx`
  (`metadata.NewOutgoingContext`, otel's `ContextWithSpan` = `context.WithValue`) whose `Err()` **is** its
  parent's (`context.go`, `valueCtx` embeds `Context`). Their texts do not change; through T2' they now claim
  the parent's message form for the child, which is the parent's own `Err()` call.
- Consumers (preconditions only, so a stronger `ctxErrsErr` only weakens them): `grpcInvokerOk`,
  `ClientConn.NewStream.wp_proof`, `waitRetryBackoff.wp_proof`.
- The standard library's own paths, checked in go1.27.3's `src/context/context.go`: `cancelCtx.err` is
  stored only by `cancel(removeFromParent, err, cause)`, whose callers pass `Canceled` (l.243, 271, 337, 648,
  657), `DeadlineExceeded` (l.647, 654), or the parent's `Err()` (l.487, 497, 512, 526: `propagateCancel`, so
  a child of a context with the two-message form has it too); `afterFuncCtx.cancel`/`timerCtx.cancel` pass
  their `err` through (l.354, 681). The `*Cause` variants (`WithCancelCause`, `WithDeadlineCause`,
  `WithTimeoutCause`) put the custom cause only in `cause` (read by `context.Cause`), never in `Err()`;
  `withoutCancelCtx.Err()` is `nil`; `emptyCtx.Err()` is `nil`.

**(a) crossWorld / (b) the persistent-authoritative fresh world.** `ctxErrsErr`/`ctxErrClient` are definitions
(WP forms), not entailments; in `W` they hold of every context, as before. The new pure facts (`ctxErrMsg m`,
`ctxErrShape e`) are given to the continuation `Φ` of `Err()`'s WP, i.e. per call, never as a Lean fact from a
resource. Re-checked 2026-11-18: no trusted entailment (axiom or premise-class field with `⊢`) has
`ctxErrsErr`, `ctxErrClient`, `ctxErrs`, `ctxOk` or `errorMsgIs` on its left (grep over `Proof`, `Spec`,
`TrustedCode`, `GooseLang`: none). So a world that builds `ctxErrsErr` with `m = "context canceled"` for any
context learns nothing it can export: the WP is vacuous there and `Φ` is never run by a real execution.
`errorMsgIs e m` stays a WP form; nothing turns it into an `errDesc` fact (no entailment
`errorMsgIs e m ⊢ ⌜errDesc e = m⌝`; the only `errDesc` source is `status.FromError`'s post, per call).

**(c) adequacy + nondeterministic allocation.** T2' is not a post; it appears inside the posts of
`withVersion`/`tracing.Start` (`ctxOk` of the derived context), where its pure facts reach a continuation
only through a real `Err()` call and then `Error()` call, and are about a string literal and dynamic types:
no address enters them (`Canceled`'s pointer varies with allocation, its message does not). Per run they hold
of Go's execution by the paths above.

**Go evidence** (`examples/axiomcx/incomingof-real/ctx_test.go`, `GOTOOLCHAIN=go1.27.3 GOWORK=off go test -v
./...`, 2026-11-18, all pass):
- `TestCtxErrOnlyTwo`: on every done context below, `Err()` is non-nil, `== Canceled` or `== DeadlineExceeded`,
  with message `"context canceled"`/`"context deadline exceeded"`, stable over calls; the custom cause shows
  only in `context.Cause`: `WithCancel`, `WithCancelCause(custom)`, `WithDeadline(past)`,
  `WithDeadlineCause(past, custom)`, `WithTimeoutCause(expired, custom)`, `WithTimeout` canceled early, a
  `WithCancel` child of a cause-canceled parent, a `WithCancelCause` child of a deadline-cause parent,
  `WithValue` over a cause-canceled parent, k8s's `channelContext` (closed), `WithCancel` over it (closed
  before and after: `propagateCancel`'s two paths), `WithCancelCause` with an `AfterFunc` registered;
  `WithoutCancel(...).Err()` is nil. Output excerpt:
  ```
  WithCancelCause(custom): Err() = *errors.errorString "context canceled"; Cause = my custom cause: ...
  WithDeadlineCause(past, custom): Err() = context.deadlineExceededError "context deadline exceeded"; Cause = my custom cause: ...
  WithCancel(channelContext closed later): Err() = *errors.errorString "context canceled"; Cause = context canceled
  ```
- `TestRpctypesErrorUnchanged` (for (2)): `rpctypes.Error` returns `Canceled`, `DeadlineExceeded` and an
  `errors.New("some other message")` unchanged; an `*errorString` whose message is `ErrFutureRev`'s (a key of
  `errStringToError`) is mapped to an `EtcdError` (so the "no key" guard is needed).
- `TestContextErrorTwice` (for (3), the blocker's shape): `ContextError(ctx, ContextError(ctx, ctx.Err()))`
  is `ctx.Err()` itself on every done context above, and on a live context for both errors.

What is not covered: a user-defined `Context` whose `Err()` returns another error. No producer makes
`ctxErrsErr` for one (Perennial's `isContext` is the context package's; `ctxErrs` is proved only for k8s's
`channelContext`), and a `cancelCtx` child of one is excluded the same way (its parent must be `ctxOk`).

### After the attack on T2' (etcd-grove-03, 2026-11-18): MINORs folded

- **M1. Not every context's `Err()` is one of the two.** etcd's own `v3rpc.cancellableContext`
  (`server/etcdserver/api/v3rpc/interceptor.go:297`) returns, after `Cancel(rpctypes.ErrGRPCNoLeader)`, the
  `*status.Error` `"etcdserver: no leader"`. The docstring therefore does not claim Go's contract for every
  context: it says the narrowed fact is **proved per producer** (the list below), names `cancellableContext`
  as excluded (it is modelled separately, `InvCancellable`/`SrvCtxWeak`, and `ctxErrShape` rejects it anyway:
  a `*status.Error` has an `Is(error) bool` method, grpc v1.84.0 `internal/status/status.go:222`; and its
  message fails `ctxErrMsg`), and says any future
  producer of `ctxErrsErr` for it must fail, by `ctxErrMsg`. The "What it claims, in Go" paragraph above is
  to be read with this: the claim is Go's contract for the contexts the producers cover, not for all.
- **M2. The other producers, each covered:**
  - `ctxErrClient_todo`, `ctxErrClient_background` (`client/v3/InvServerKV.lean`), `ctxErrClient_quiet`
    (`InvClientAuth.lean`): `Err()` returns `nil` on every call (an `emptyCtx`, or `ctxQuiet`'s nil `Err()`);
    only the `nil` disjunct is produced, the message form is never reached.
  - `clientWatchOk_ctxErr` (k8s `etcd3/WatchCons.lean`), `storeWatchOk_ctxErr` (examples k8s
    `etcd3/watchEvents.lean`), `ctxErrClientAll_of_kvWatcher` (`client/v3/KMClient.lean`): project the stored
    `ctxErrClientAllW` out of the client watcher's `watchSrvFacts`, which is made by `ctxErrClientAllW_of`
    (from `context.ErrAny`); no new claim.
  - `isNewClient_ctxOk` (`client/v3/InvClientNewResult.lean`): projects the client context's facts out of
    `isNewClient`, made by `New`'s proof from a `WithCancel` of the caller's context (an `isContext`, so from
    `ErrAny` again) or a quiet context.
- **M3.** `examples/axiomcx/incomingof-real/go.mod` pins grpc v1.84.0 (as `examples/axiomcx/incomingof`);
  rerun 2026-11-18, `GOTOOLCHAIN=go1.27.3 GOWORK=off go test -v ./...`: all five tests pass
  (`TestCtxErrOnlyTwo`, `TestRpctypesErrorUnchanged`, `TestContextErrorTwice`, `TestRealTypes`,
  `TestContextErrorRaw`).

### (2), (3): planned proved-spec changes (no trusted text)

- `rpctypes.Error.spec` gains a post conjunct: for `err = ok e` with no `GRPCStatus` method and
  `errorMsgIs e m` with `m` no key of `errStringToError` (from `rpctypesInit`'s literal table), `err' = err`.
  Form (premise carried as a wand in the post, so existing callers are unaffected):
  `□ (∀ e m, ⌜err = GoInterface.ok e ∧ noGRPCStatus e.ty ∧ m ∉ errStringKeys⌝ -∗ errorMsgIs e m -∗ ⌜err' = err⌝)`
  (exact names fixed when implemented).
- `ContextError.spec`: the ctx disjunct carries `ctxErrMsg m ∗ errorMsgIs e m`, and a new conjunct
  `□ (ctxErrIs err -∗ ctxErrIs err')` with `ctxErrIs err := ∃ e m, ⌜err = ok e ∧ ctxErrMsg m ∧ ctxErrShape e
  ∧ noGRPCStatus e.ty⌝ ∗ errorMsgIs e m`, so `kv.Get`'s second call keeps `kv.Do`'s context error.

### T8 (new, found implementing (2), 2026-11-18): `status.FromError.spec` needs "no `GRPCStatus` → `ok = false`" — STOP

**Why.** (2) needs `rpctypes.Error`'s lookup key `d = ErrorDesc(e)` to be `e`'s message `m` (`errorMsgIs e m`):
then the result is `e` unchanged (no key) or an `EtcdError` of description `d = m` (a key), and with `m` a
context message (`ctxErrMsg`, so no handler description) the Range outcome holds in both cases.
`ErrorDesc.spec` gives only `d = errDesc e`; `FromError.spec`'s last conjunct gives `errorMsgIs e m -∗
⌜errDesc e = m⌝` **only when `ok = false`**, and nothing in `FromError.spec` says when `ok` is `false`. So
without a new trusted fact `errDesc` of a context error stays unknown (the point of Part B) and `kv.Get`'s
second `ContextError` cannot be shown to keep the outcome. No proof-only route exists: `errDesc` has no other
per-run source. (Key facts about `errStringToError`, the alternative the attack mentioned, would not suffice
alone either: they speak of `d`, still unlinked to `m`.)

**Proposed text** (`Spec/google_golang_org/grpc/status/FromError.lean`, a new post conjunct of the axiom
`status.FromError.wp_proof`; the rest unchanged):
```lean
      -- (incomingof Part B, T8) a leaf error without grpc's `GRPCStatus() *Status` is no status error
      ⌜∀ e : GoInterfaceOk, err = GoInterface.ok e →
        methodSet e.ty !! go!"GRPCStatus" ≠
          some (go.Signature [] false
            [go.GoType.PointerType google_golang_org.grpc.internal.status.Status.ty]) →
        ok = false⌝
```
(The signature is `grpcErrMethodsOk`'s, `cache/v3/Base.lean:354`.)

**Why true in Go** (grpc v1.84.0 `status/status.go:96-127`): for a non-nil `err`, `ok = true` only through
`err.(grpcstatus)` (the dynamic type has `GRPCStatus() *Status`) or `errors.As(err, &gs)`; the precondition
`statusErrOk err` makes `err` a leaf (`errors.isLeafError`: no `Unwrap`, no `As`), so `errors.As` checks only
`err` itself against the same interface, which fails as well. Both `true` returns are guarded by the method;
the `grpcStatus == nil` branches return `false`.

**Checks.** (a)/(b): a triple's post, not an entailment; in `W` the triple is vacuous and exports nothing.
(c): grpc's `status` is names-only (uninterpreted), so no closed program's adequacy reaches this post; and the
fact is about the dynamic type's method set and a boolean, with no address in it. No consumer changes
meaning: the conjunct is new, read only by `ErrorDesc`/`rpctypes.Error`'s proofs.

**Go evidence** (`examples/axiomcx/incomingof-real/ctx_test.go` `TestFromErrorNoGRPCStatus`, go1.27.3, grpc
v1.84.0, passes): `FromError` returns `ok=false` and the message `Error()` for `Canceled`, `DeadlineExceeded`,
an `errors.New`, a leaf struct whose message is a handler description, and a type with a `GRPCStatus() int`
method (another signature); `ok=true` for a `*status.Error` (the guard is needed).

**Decided by etcd-grove-03 (2026-11-18):** T8 approved pending a short independent attack (not added to the
axiom until the verdict); the weaker forms of (2) (`err' = err ∨ errDesc err' = m`) and (3) (a context error
comes back as one, or with a context-message description) ACCEPTED.

**Plan with T8** (all proved, no further trusted text):
- `ErrorDesc.spec` gains `□ (∀ e m, ⌜err = ok e ∧ noGRPCStatus e.ty⌝ → errorMsgIs e m -∗ ⌜d = m⌝)`.
- `rpctypes.Error.spec` gains `□ (∀ e m, ⌜err = ok e ∧ noGRPCStatus e.ty⌝ → errorMsgIs e m -∗
  ⌜err' = err ∨ errDesc err' = m⌝)` — weaker than the decided wording (2) ("comes back unchanged" when `m` is
  no key), which would also need the 57 keys in the trusted `errStringToError_init` (another trusted text);
  the disjunction suffices because `rangeErrΨ` holds vacuously at a non-handler description.
- `ContextError.spec`: the ctx disjunct carries `ctxErrIs err'` (`∃ e m, ⌜err' = ok e ∧ ctxErrMsg m ∧
  ctxErrShape e⌝ ∗ errorMsgIs e m`), and a new conjunct `□ (ctxErrIs err -∗ ctxErrIs err' ∨
  ⌜ctxErrMsg (errDesc err')⌝)`. `noGRPCStatus` of a ctx-shaped client error is derived (a `*status.Error` has
  `Is`, so `ctxErrShape` leaves `*errorString`/`deadlineExceededError`, whose method sets lack `GRPCStatus`).
- `kv.Get`: the second call keeps `kv.Do`'s outcome (description kept), or the ctx disjunct, or a context
  message description, where `rangeErrΨ` is vacuous.

## Trust-base delta (expected)

- Axioms: none added or removed (`incomingOf_cancelCtx` stays: Part A is not linked).
- Trusted texts changed: `ContextReadErrs` (field `descs` → `descDeadline`), `ctxErrsErr`/`ctxErrClient`
  (conjunct), `errors.IsStatusErr.spec` (post). Unchanged but re-justified: `waitRetryBackoff.spec`,
  `grpcInvokerOk`.
- Exported statement text changed: `client_range_any` (through `rangeErrOut`). Closed statements: none (the 50
  closed theorems' `Hctx : ContextReadErrs` keeps its text, with one field fewer).
