# Scope: per-run restatement of the incoming-metadata axioms (A) and of the context errors' descriptions (B)

**APPROVED BY THE USER, 2026-11-17, via etcd-grove-03, and prioritized ahead of other tracks:** Part A as
recommended (A-C, variant C-ii; Q1 A-C now, A-D later as its own Scope; Q2 `srvRawStreamIs`; Q3 delete
`incomingOf_wrapper`, apply the axiom directly; Q5 A first; Q6 restate `v3rpc.incomingOf_cancellableContext`
in place, delete `incomingOf_cancelCtx`); then B0 (read-only inventory), STOP; Part B only after
etcd-grove-03's go. Final texts and the cross-world argument: `notes/axiom-review/incomingof.md`.

**Part A REFUTED (2026-11-17, independent attack by etcd-grove-03): not linked, Lean reverted on this branch.**
A fresh world owning a persistent authoritative heap builds `incomingKept` (`notes/axiom-review/incomingof.md`,
"The refutation"). The user decided: B0 next, then STOP; Part B only after 03's go, its new texts checked
against the persistent-auth fresh-world attack first; the per-heap redesign (`incomingIs`, `errDesc`
analogue) gets its own Scope.

**Part B APPROVED BY THE USER, 2026-11-17, via etcd-grove-03:** (1) delete `ContextReadErrs`' `Canceled` half
(`descDeadline` stays); (2) `ctxErrsErr`'s conjunct in message form, server per-run facts from
`toGRPCErrorMap_init`'s conjuncts; (3) the context-error case in the client's Range error outcome
(`client_range_any`'s text changes; exact old → new at the land stop), ruled out by k8s Get/List; (4)
`errors.IsStatusErr.spec` strengthened for an `EtcdError` target. Also decided: land the branch with Part A's
revert (5dab7c3336) as is. Exact texts and the soundness note (crossWorld, persistent-auth fresh world, §0.2):
`notes/axiom-review/incomingof-b.md`; stop for the independent attack before implementing. Deviation for
review: (4) is guarded by "no `Is` method" (the literal form is false in Go, `TestIsEtcdTarget`).
Forms decided by the agent (reviewed at checkpoint): `metadata.incomingKept_apply` (A1) not added, and
`incomingOf_cancelCtx_parent_unique`/`v3rpc.incomingOf_cancellableContext_field_unique` deleted: nothing
would use them (the restated axiom takes `incomingKept` directly).

2026-11-17, incomingof agent of etcd-grove-03. Branch `incomingof-scope` off `lean` `3cd4b72599`. Notes only;
no Lean changed. Part A was approved by the user on 2026-11-17 ("restate both axioms per execution"). Part B
was added on the same day, also approved by the user via etcd-grove-03 (the Hctx repair, blocker B1 of
`notes/soundness-1117-handoff.md` on branch `soundness-1117`).

Finding: branch `axiom/ctx-descs` (4cfaf29628) has `notes/axiom-review/ctx-descs.md` and
`Proof/github_com/mit_pdos/etcd_grove/examples/axiomcx/ctxdescs/CrossWorld.lean`. The lemma `crossWorld` and
the theorem `incomingOf_const` there are proved.

Go evidence: `/shared/tmp/incomingof/gotest/md_test.go`, grpc v1.84.0, run with GOWORK=off, all tests pass
(the output is quoted where it is used).

---

## 0. The rule that decides both parts

Take a law whose conclusion is a pure fact `⌜f v = …⌝`, where `f` is an opaque Lean function (`incomingOf`,
`errDesc`) and `v` is a value that contains a pointer, so its Go meaning depends on the heap. Such a law is
sound in the per-execution reading only if both of these hold:

1. **Not an entailment from a resource that can be built on its own.** By `crossWorld`, a resource made of
   persistent points-tos, or of WP forms over code that is proved, can be put in a fresh heap at any address
   with any content. Its conclusion then becomes a Lean fact for every address. This is the flaw in both
   axioms of A and in `descs` (B).
2. **Not a triple post over code that has Lean semantics.** Allocation is nondeterministic over every fresh
   address (`Perennial/GooseLang/Lang.lean:750,834`, `AllocS`). So the adequacy theorem for a closed program
   whose post states `⌜f c = f p⌝` about a freshly allocated `c` gives that fact for every address `c` the
   allocator can return. A second program that allocates at the same address over another parent then
   joins the two. Not formalized, because it needs a Lean proof that an execution exists; but it is true of
   the model.

   This rules out the brief's option "a law in the post of `WithCancel` / `newCancellableContext`": both
   functions are translated code with Lean semantics. `WithCancel` is also proved in Perennial, so a trusted
   triple about it would be a twin spec, which the standing rule forbids.

What remains sound in the repository's accepted per-execution reading:
- facts about uninterpreted code: the posts of `FromIncomingContext.spec`, `WithValue.spec`,
  `Tracer.Start.spec`, `toGRPCErrorMap_init`, `status.FromError`'s wand, and the posts of the grpc model
  axioms;
- facts that come only from such posts (the opaque or trusted predicates they deliver, which no proof can
  build);
- location-free pure facts (`errDesc_etcdError`, and `DeadlineExceeded`'s description).

A further point, which neither the review nor the brief raised. Even a law that is guarded in this way, with
a pure conclusion and a points-to in its antecedent, still claims something about hypothetical cells in the
all-resources model of Iris. So it is true only under that same per-execution reading, not in the model.
The only fully sound form is a conclusion that is not pure: a per-heap IProp (option A-D below). This
applies to every `incomingOf` and `errDesc` fact in the repository, not only to the two axioms. It is open
question Q1.

---

## Part A: `incomingOf_cancelCtx` and `v3rpc.incomingOf_cancellableContext`

### A.1 Uses

| what | file:line |
|---|---|
| `axiom incomingOf_cancelCtx` | `Proof/google_golang_org/grpc/metadata/Incoming.lean:61` (docstring :38-60) |
| `incomingOf_cancelCtx_parent_unique` (proved, no other user) | `Incoming.lean:68` |
| `axiom v3rpc.incomingOf_cancellableContext` | `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/WrapperMd.lean:76` (docstring :59-75) |
| `v3rpc.incomingOf_cancellableContext_field_unique` (proved, no other user) | `WrapperMd.lean:89` |
| `v3rpc.incomingOf_wrapper`, the only theorem that applies the two axioms | `WrapperMd.lean:106` and `:107` |
| **the only consumer**: `incomingOf (ccCtx l) = incomingOf ci`, fed to the stream handler hypothesis `Hk` (`streamHandlerCall` at `incomingOf ci`, InvGrpcStream.lean:1081/1111) | `.../v3rpc/newStreamInterceptor.lean:372` (and `:220`, the hypothesis' form) |
| `v3rpc.wp_WithCancel_cancelCtx` (keeps `ctxField c ↦□ parent`; it does not use the axioms) | `WrapperMd.lean:121`; used at `newCancellableContext.lean:43` |
| `etc/tcb-baseline.txt` | lines 583, 857 |

**Collections.** The same 22 list both axioms: auth3, authN, authkv, cachekv, compactkv, k8scompactor,
k8setcd3, leaseN, leasecatchup, leaseexpiry, leaseexpiryN, leasekv, linkv3p, linkvtxn, m2, putget, putget3,
putgetN, txnlinfaultsN, v3rpc, watch, watchkv (`grep -l incomingOf_cancel etc/tcb-collections/*.txt`). These
are the results that reach the stream interceptor through v3rpc's `Link`: every closed etcd and k8s theorem
that serves the watch stream.

**Closed statements.** No `Results.lean` or `Adequacy*.lean` statement mentions `incomingOf`; v3rpc's
`Results.lean:944-1138` mentions it only inside proofs. `srvRawStreamIs` is in no closed statement. So no
closed statement's text changes.

### A.2 Options weighed

| option | verdict |
|---|---|
| A-A: a law in the post of `WithCancel` (a trusted triple) or of `newCancellableContext` | **Rejected.** It is code with Lean semantics, so §0.2 applies: adequacy plus nondeterministic `Alloc` transfer the pure post across executions. Also a twin spec of Perennial's proved `WithCancel`. |
| A-B: `incomingOf` keyed by a ghost name allocated with the context | **Rejected.** The name would have to come from a trusted spec of `WithCancel` (same problem as A-A). A key on the heap's ghost name hides the law from `crossWorld` (fresh names only), but in the model it is still false at every resource (§0, last paragraph); this only hides the problem. |
| A-C: **the law in grpc's trusted delivery of the stream's run context**, structural (an exact parent cell), with the wrapper's link guarded by it | **Recommended now.** Both antecedents need a fact that only an uninterpreted grpc call delivers, so neither `crossWorld` nor adequacy reaches it. The two axioms become one trusted conjunct plus one guarded axiom (C-ii). Small. |
| A-C-iii: grpc's law over `ctxValueFrom ci x` or `valueAt` (Value-behaviour, no structure), which would make the wrapper's link a theorem | **Rejected.** A context `L` whose `Value` loops satisfies `ctxValueFrom p L` and `valueAt L k R` for every `R` (partial correctness). With two streams in one run, the law equates `incomingOf ci1 = incomingOf L = incomingOf ci2`, and that is derivable inside the logic. This is the same attack that refuted T-b. Only a structural link (one parent cell) blocks it. |
| A-D: replace the pure `incomingOf` by a per-heap persistent IProp `metadata.incomingIs x md`, defined through Perennial's `ctxValue` at `mdIncomingKey{}` and an opaque `mdHeld v md` (grpc's frozen `MD` value) | **Principled, recommended as the follow-up (Q1).** Both links become theorems: `ctxValue_cancel`, and `v3rpc.valueAt_cc`'s argument. The loop case is harmless, because `FromIncomingContext(L)` never returns either. It removes the per-run fiction for every metadata fact. But it changes about 41 files: every handler spec's `Spec (incomingOf ci)`, `InvGrpc`/`InvGrpcRun`/`InvGrpcStream`, `FromIncomingContext`/`WithValue`/`Tracer.Start`/`EnsureTrace`, auth's `ctxTokenOf`, and the server's `Hinc` lemmas. Estimate 2-3 weeks. |

### A.3 New texts (A-C, variant C-ii)

**(1) `Incoming.lean`.** Delete `axiom incomingOf_cancelCtx` (:38-64) and `incomingOf_cancelCtx_parent_unique`
(:66-73). Add a defined (not opaque) per-run predicate with the law as a theorem:

```lean
/-- **`ci`'s `*cancelCtx` children have its incoming metadata** (persistent; per run): every `*cancelCtx`
`c` whose `Context` field holds `ci` (`WithCancel(ci)`: `propagateCancel` writes the field once,
Go `src/context/context.go:477,514`) answers `FromIncomingContext` as `ci` does
(`(*cancelCtx).Value(mdIncomingKey{})` is `value(c.Context, key)`; grpc v1.84.0 `metadata.go:268-282`).
Not an axiom: a conjunct of grpc's delivery of a run context (`srvRawStreamIs`), so only an uninterpreted
grpc call gives it; no proof can build it (its conclusion is a pure fact about the opaque `incomingOf`). -/
def metadata.incomingKept (ci : GoInterfaceOk) : IProp GF :=
  iprop(□ ∀ c : Loc, _root_.Perennial.context.ctxField c ↦□ (GoInterface.ok ci) -∗
    ⌜metadata.incomingOf (GoInterface.ok (interface.mk
        (go.GoType.PointerType _root_.Perennial.context.cancelCtx.ty) #c)) =
      metadata.incomingOf (GoInterface.ok ci)⌝)
-- + Persistent instance; theorem metadata.incomingKept_apply (proved, the wand's application)
```

**(2) `Proof/google_golang_org/grpc/InvGrpcStream.lean:448` `srvRawStreamIs`** (trusted text; made only by the
grpc model through `InvGrpcRun.lean:157`). Old last line:

```lean
    context.isContext ci cd ∗ grpcRunCtx ci ∗ context.libCtxOkC ci ∗ trace.spanCtxOkC ci ∗
    http.netCtxOkC ci)
```
New:
```lean
    context.isContext ci cd ∗ grpcRunCtx ci ∗ context.libCtxOkC ci ∗ trace.spanCtxOkC ci ∗
    http.netCtxOkC ci ∗ metadata.incomingKept ci)
```
Add a docstring sentence: grpc's run context `ci` is a context whose incoming metadata
`FromIncomingContext` reads through `Value(mdIncomingKey{})`; a `*cancelCtx` over it answers that key as `ci`
does (Go test `TestWrapperInheritsIncoming`). `InvGrpcStream.lean` already reaches `Incoming.lean` (it states
`Spec (metadata.incomingOf ci)`), so no new import.

Why `srvRawStreamIs` and not `grpcRunCtx`: `grpcRunCtx` is also in the unary run, the client's handler
contexts and about 20 handler specs, and none of them needs the law. `srvRawStreamIs` has one producer (the
model) and one consumer (the interceptor). See Q2.

**(3) `WrapperMd.lean:76`, `v3rpc.incomingOf_cancellableContext`.** Same name, restated (trusted). Old:

```lean
axiom v3rpc.incomingOf_cancellableContext (l : Loc) (c : GoInterfaceOk) :
    (v3rpc.ccField l ↦□ (GoInterface.ok c) : IProp GF) ⊢ (iprop(⌜metadata.incomingOf
      (GoInterface.ok (v3rpc.ccCtx l)) = metadata.incomingOf (GoInterface.ok c)⌝) : IProp GF)
```
New: guarded by the run context's fact; the parent is exactly a `*cancelCtx` over `ci`:
```lean
axiom v3rpc.incomingOf_cancellableContext (l c : Loc) (ci : GoInterfaceOk) :
    (metadata.incomingKept ci ∗ _root_.Perennial.context.ctxField c ↦□ (GoInterface.ok ci) ∗
      v3rpc.ccField l ↦□ (GoInterface.ok (interface.mk
        (go.GoType.PointerType _root_.Perennial.context.cancelCtx.ty) #c)) : IProp GF) ⊢
    (iprop(⌜metadata.incomingOf (GoInterface.ok (v3rpc.ccCtx l)) =
      metadata.incomingOf (GoInterface.ok ci)⌝) : IProp GF)
```
Docstring: the old Go argument (`interceptor.go:270-283`: `Value` is promoted, the field is written once by
the composite literal), plus why it is guarded (§A.4). `field_unique` stays.

`v3rpc.incomingOf_wrapper` (:106) becomes the axiom itself (one application). Its statement gains
`metadata.incomingKept ci` and loses nothing. Alternatively delete it and apply the axiom directly in the
interceptor.

**(4) `newStreamInterceptor.lean`.** At :258 the `icases Hss'` pattern gains `#Hkept`. At :372,
`v3rpc.incomingOf_wrapper l c ci $$ [Hkept Hcf Hfield]`. :118 (the other `iunfold srvRawStreamIs`) gets one more
`-` in its pattern.

**(5) Trust base.** `etc/tcb-baseline.txt` loses `axiom incomingOf_cancelCtx` (line 583) and keeps
`v3rpc.incomingOf_cancellableContext` (restated). The 22 collections lose one axiom line each
(`etc/tcb-report.py --collection … --check --update`). Trusted text changed: `srvRawStreamIs`'s definition.
Regenerate the interfaces of the API lists that cover `Incoming`/`WrapperMd`/`InvGrpcStream`, if any
(`etc/gen-interface.py`).

### A.4 The crossWorld check of the new texts

- `incomingKept ci` is a defined persistent wand with a pure conclusion. To build it in a fresh world you
  must prove `∀ c, incomingOf (cancelCtx c) = incomingOf ci` in Lean, which nothing provides (`incomingOf` is
  opaque). It is produced only by the grpc model axioms (`Spec/google_golang_org/grpc/model/*`, through
  `grpcAccepted`), which are triples about uninterpreted grpc calls (`runStream`). No closed Lean program
  reaches their posts, so adequacy cannot export it (§0.2).
- Restated v3rpc axiom: its antecedent contains `incomingKept ci`, so it is out of reach for the same reason.
  The `ctxField`/`ccField` points-tos alone conclude nothing.
- The loop attack: the links are structural. `c`'s parent cell holds exactly `ci`, and `l`'s cell holds
  exactly `cancelCtx c`. A looping `L` is equated with nothing, because no law takes a `Value` WP.
- Two streams in one run (two `ci`s with different metadata): each real `c` has one parent cell, so the
  logic derives no equation between `ci1` and `ci2`. In the all-resources model, `incomingKept ci1 ∗
  incomingKept ci2` at a thread resource forces `incomingOf ci1 = incomingOf ci2`, through a hypothetical
  fresh cell. It is not derivable: a WP proof sees only entailments, and at a step the authoritative heap
  rules the extension out. It is the same per-run reading as `FromIncomingContext.spec`'s post. Q1 is the
  fix for it.

### A.5 Go evidence

`TestWrapperInheritsIncoming`: for two tokens, the `*cancelCtx` over `NewIncomingContext(…, token)` and
etcd's `cancellableContext` shape over it both return that token from `FromIncomingContext` ("token tokA:
WithCancel child and wrapper carry it"; the same for tokB). `TestIncomingNotConstant`: two `*cancelCtx`s in one
run answer differently ("cancelCtx over md: ok=true; over Background: ok=false"). This contradicts
`incomingOf_const`, so the old axiom is refuted against grpc.

### A.6 Steps and estimate (A-C)

| step | lines |
|---|---|
| A1 `Incoming.lean`: delete the axiom and `parent_unique`; add `incomingKept`, its instance and `_apply` | ~40 |
| A2 `srvRawStreamIs`: the conjunct and docstring; import check | ~15 |
| A3 `WrapperMd.lean`: restate the axiom; rewrite or delete `incomingOf_wrapper`; header comment | ~35 |
| A4 `newStreamInterceptor.lean`: two patterns, one application | ~10 |
| A5 build of the touched leaves (`etc/importers.py --uses srvRawStreamIs`), tcb baseline and 22 collections, interfaces, STATUS, audit rows | ~60 |

Total about 160 lines, 1 day (build time dominates).

---

## Part B: `ContextReadErrs.descs` and `ctxErrsErr`'s description conjunct

### B.1 Uses

| what | file:line |
|---|---|
| `class ContextReadErrs`, field `descs` (Canceled half flawed, DeadlineExceeded half sound) | `Proof/go_etcd_io/etcd/server/v3/etcdserver/read/Init.lean:70-86` |
| `descs` used, client: `ctxErrClientAllW_of` | `Proof/go_etcd_io/etcd/client/v3/ErrorsNewOk.lean:254` (the conjunct at :297, :306) |
| `descs` used, client: `chanCtx_ok` | `Proof/go_etcd_io/etcd/client/v3/ChanCtx.lean:166` (:219) |
| `descs` used, server: v3rpc `initialize'` → `ctxErrDescs` | `.../api/v3rpc/Init.lean:296`; def `.../v3rpc/Base.lean:230`; in `v3rpcInit` `Base.lean:284`; unfold `Init.lean:384` |
| `ctxErrDescs` consumer: `rangeErrOther_facts` (needs `rangeErrMsgOk (errDesc x)` of a passed context error) | `.../v3rpc/ServerKVOn.lean:802-820` |
| `ctxErrsErr` (trusted grpc-model text, HS-5 (a)); its conjunct `⌜err = nil ∨ errDesc err ∉ handlerDescs⌝` | `Proof/google_golang_org/grpc/InvGrpc.lean:1419`, conjunct :1431; client copy `ctxErrClient` `InvKVConn.lean:1600` |
| callers of the two producers (no per-run source) | `TimeoutCtx.lean` (3), `InvClientNewResult.lean` (3), `InvClientAuth.lean`, `InvGrpc.lean` (1), k8s `compactor__runCompactLoop.lean` (2), `compactor__runWatchLoop.lean` (2), examples `auth/{Run,reqCtx}`, `auth3/{barrier,run}`, `authN/{barrier,run}` |
| `ContextError.spec` post (`errDesc err' = errDesc err ∨ errDesc err' ∉ handlerDescs`) | `Spec/go_etcd_io/etcd/client/v3/ContextError.lean:44-45`; consumers `kv__Do.lean:126`, `kv__Get.lean:80` (through `ifcErrOut_desc`, `InvKVConn.lean:1403`) |
| `waitRetryBackoff.spec` post (`err = nil ∨ errDesc err ∉ handlerDescs`) | `Spec/go_etcd_io/etcd/client/v3/waitRetryBackoff.lean:40`; consumer `Client__unaryClientInterceptor.lean:247` (`ifcErrOut_notin`, `InvKVConn.lean:1377`) |
| `ifcErrOut` → exported KV error outcomes (`rangeErrΨ_of_ifc` and its siblings) | `InvKVConn.lean:1370`; `KVService.lean:1031-1050`; `client/v3/Results.lean:1514` |
| `ContextReadErrs` in closed statements (`Hctx : ∀ hG, ContextReadErrs …`) | 50 `Results`/`Adequacy` files (list in `ctx-descs.md`, "Results that take ContextReadErrs") |

`ctxErrClient`/`ctxOk` are in the preconditions of `client/v3/Results.lean`'s exported triples (:2798, :2872,
:2925, :3096). Those statements name the predicate, so their text does not change, but their meaning does
(see B.6).

### B.2 New texts

**(1) `read/Init.lean:76-86`, `descs` → `descDeadline`** (a premise field; trusted text). Old: the two-half
entailment quoted in B.1. New, location-free and pure (no resource):

```lean
  /-- `DeadlineExceeded`'s gRPC description (k8s etcd3 7c-2 part 2, S1; restated 2026-11-17, ctx-descs
  review): its value is `deadlineExceededError{}` (`context.isInit`'s `HDeadlineExceededTy`), not a status
  error, so `status.FromError` gives its `Error()`, `"context deadline exceeded"` (`context.go`). A fact of
  the value, the same in every run (an empty struct: no location). `Canceled`'s half is gone: its value is a
  `*errorString` pointer, and a pure fact about `errDesc` of a pointer, from points-tos, holds of every
  location (`crossWorld`). -/
  descDeadline : go_etcd_io.etcd.cache.v3.errDesc
      (interface.mkOk _root_.Perennial.context.deadlineExceededError.ty
        #(zero_val _root_.Perennial.context.deadlineExceededError)) = go!"context deadline exceeded"
```
The class keeps `errs`. The closed theorems' `Hctx` keeps its text and is weaker, because the class has one
field fewer and the remaining field is a pure fact of one value (Go `TestCtxErrDescs`).

**(2) `v3rpc/Base.lean:230`, `ctxErrDescs`** (not trusted: a definition in `v3rpcInit`). New: only what the
consumer needs, per run:

```lean
def ctxErrDescs : IProp GF :=
  iprop((∃ e : GoInterface, globalAddr _root_.Perennial.context.Canceled ↦□ e ∗
      ⌜rangeErrMsgOk' (go_etcd_io.etcd.cache.v3.errDesc e)⌝) ∗
    (∃ d : GoInterface, globalAddr _root_.Perennial.context.DeadlineExceeded ↦□ d ∗
      ⌜rangeErrMsgOk' (go_etcd_io.etcd.cache.v3.errDesc d)⌝))
```
Here `rangeErrMsgOk' m := m ≠ futureRevDesc ∧ m ≠ compactedDesc`. That is `ReadOn.lean:288`'s
`rangeErrMsgOk`, inlined or moved to `cache/v3/Base` (a form decision). It is proved at `Init.lean:296` from
`toGRPCErrorMap_init`'s post: `grpcErrMapOk`'s "`errDesc k ≠ futureRevDesc ∧ ≠ compactedDesc`" for every key,
and `Canceled`/`DeadlineExceeded` are keys (`grpcErrKeyGlobals`, `Base.lean:118-119`). That post is a triple
about the uninterpreted `toGRPCErrorMap.init`, a per-run source. Consumer `ServerKVOn.lean:820-826`: `hctx`
becomes those two facts directly, with no `decide` on the strings.

**(3) `InvGrpc.lean:1431`, `ctxErrsErr`'s conjunct** (trusted grpc-model text, HS-5 (a); the client copy
`InvKVConn.lean:1600` changes the same way). Old:
```lean
        ⌜err = interface.nil ∨ go_etcd_io.etcd.cache.v3.errDesc err ∉ handlerDescs⌝ -∗ Φ #err) -∗
```
New (recommended direction (A)): `Error()` stably returns some message that is no handler's:
```lean
        (⌜err = interface.nil⌝ ∨ ∃ (e : GoInterfaceOk) (m : GoString), ⌜err = GoInterface.ok e⌝ ∗
          go_etcd_io.etcd.cache.v3.errorMsgIs e m ∗ ⌜m ∉ handlerDescs⌝) -∗ Φ #err) -∗
```
Docstring: grpc's `status.FromContextError(ctx.Err())` (the invoker on a done context) keeps the message
(`TestCtxErrDescs`: `FromContextError(Canceled)`: code=Canceled msg="context canceled").

Producers, proved per run with no premise. For `Canceled`: `isInit`'s `HCanceledCell` (`x.s ↦□ "context
canceled"`) plus `errorString.Error`'s proved WP give `errorMsgIs`. For `DeadlineExceeded`: its `Error()`
method body (goose emits it; check its WP, risk R3).

**(4) `waitRetryBackoff.spec`.** Text unchanged. Its proof gets the message from the WP of `Error()` that
`contextErrToGRPCErr` calls, then `status.Error(code, m)`'s post gives `errDesc = m`, per run (grpc status is
uninterpreted). Check that the status constructor's spec gives `errDesc`; if not, that is risk R2.

**(5) `ContextError.spec`'s last conjunct** (a proved spec; a stop item only because exported posts depend
on it). The context branch returns the raw `ctx.Err()`, which the client never passes to `status.FromError`.
So no per-run source of `errDesc err'` exists there. New:
```lean
      ⌜err ≠ GoInterface.nil⌝ -∗ (⌜errDesc err' = errDesc err⌝ ∨
        ∃ (e' : GoInterfaceOk) (m : GoString), ⌜err' = GoInterface.ok e' ∧ m ∉ handlerDescs ∧
          e'.ty ∈ ctxErrTys⌝ ∗ errorMsgIs e' m)
```
Here `ctxErrTys` = {`*errors.errorString`, `context.deadlineExceededError`}: a type fact, location-free.

**(6) `ifcErrOut` (`InvKVConn.lean:1370`) and the KV error outcomes.** `ifcErrOut_desc` can no longer get
`errDesc err' ∉ handlerDescs` in the context branch. `ifcErrOut` gains the per-run disjunct `ctxErrMsg err`
(the existential above). `rangeErrΨ_of_ifc` (`KVService.lean:1031`) and its siblings for
Put/Txn/DeleteRange/Compact must then produce their outcome at `errDesc err` from that disjunct, and they
can't: `rangeErrΨ d` is two wands with premises `d = futureRevDesc`/`d = compactedDesc`, which a raw error of
unknown `errDesc` cannot refute. **This is the crux of Part B.** Three ways:
- (B-i, recommended) the exported KV outcomes become `Ψe (errDesc err) ∨ ctxErrMsg err`. Every consumer
  either reaches a `status.FromError`/`rpctypes.ErrorDesc` call on the error, where `FromError`'s wand turns
  `errorMsgIs e m` into `errDesc err = m ∉ handlerDescs`, or compares it with `rpctypes` `EtcdError` values,
  where the dynamic types differ. This changes exported client specs (not closed statements). It needs
  inventory B0 first.
- (B-ii) key the outcome obligations by type (only `EtcdError`, location-free `desc`). This is cleaner but a
  larger redesign of the client error vocabulary.
- (B-iii) a per-run `errDesc` of `Canceled` taken from an untranslated package's init axiom (for example
  grpc `status`'s). **Rejected**: if `isPkgInit`'s content can be built on its own (the reading `read/Init`'s
  docstring gives), it is `descs` again; and even if not, the trusted text would claim a fact about another
  package's cell.

### B.3 The crossWorld check of the new texts

- `descDeadline`: pure, about one closed value with no location. There is nothing to transfer. Per run,
  `FromError`'s wand agrees with it (Error() returns the literal).
- `ctxErrDescs`: a defined conjunct of `v3rpcInit`, obtained only through v3rpc's `initialize'`, whose source
  is the post of `toGRPCErrorMap_init` (uninterpreted). It is not an entailment axiom.
- `ctxErrsErr`'s new conjunct: an IProp (`errorMsgIs`, a WP form) and a pure fact about a string `m`. Nothing
  pure about `errDesc` of a pointer. The loop case: `errorMsgIs e m` holds for every `m` when `Error()` loops.
  That is harmless, because the only `errDesc` link is `FromError`'s wand, in the post of a call that then
  never returns.
- `ContextError.spec`/`ctxErrMsg`: the same, plus a type fact (location-free).
- Not allowed (checked): any `errorMsgIs e m ⊢ ⌜errDesc (ok e) = m⌝` entailment. `crossWorld` at `x.s ↦□ "a"`
  and `↦□ "b"` gives `False` (ctx-descs.md, last row of the family table).

### B.4 Go evidence

`TestCtxErrDescs`: `*errors.errorString "context canceled"`: FromError ok=false code=Unknown msg="context
canceled"; `context.deadlineExceededError "context deadline exceeded"`: msg="context deadline exceeded";
`FromContextError(Canceled)`: code=Canceled msg="context canceled".

`TestErrorStringDescByCell`: two `errors.New` values of one dynamic type have different descriptions, and a
user's `errors.New` with a handler description's text has that description. So `errDesc` of an
`*errorString` depends on its cell, not its type. This is why no pure fact about `Canceled`'s description
can be stated, and why `∀ x, errDesc (*errorString x) ∉ handlerDescs` would be false.

### B.0 Inventory (read-only, 2026-11-17, at lean 5fb716b5eb): the consumers of the client's KV error outcome

**Only `Range` has an error outcome.** `ifcErrOut` appears in the specs of `kVClient.Range` and
`retryKVClient.Range` only; Put/Txn/DeleteRange/Compact carry none. So the "siblings" of `rangeErrΨ` in B.2(6)
and B5 do not exist. The outcome's compacted half has no client-side consumer (`k8s.rangeErrSound` keeps the
future half only).

The chain, producer to closed theorems:

| step | file:line | what it does with `errDesc err` |
|---|---|---|
| retry interceptor | `client/v3/Client__unaryClientInterceptor.lean:199-544` (`ifcErrOut_of_attempt`), `:247` (`ifcErrOut_notin`, from `waitRetryBackoff.spec`'s `errDesc err ∉ handlerDescs`) | produces `ifcErrOut` |
| `kVClient.Range`, `retryKVClient.Range` | `Spec/.../etcdserverpb/kVClient__Range.lean:48`, `Spec/.../client/v3/retryKVClient__Range.lean:42` | pass it on |
| `kv.Do` (ContextError) | `client/v3/kv__Do.lean:126`, `kv__Get.lean:80` (`ifcErrOut_desc`, from `ContextError.spec`'s `errDesc err' = errDesc err ∨ ∉ handlerDescs`) | moves it to the returned error |
| `kv.Get` | `client/v3/kv__Get.lean:123-125` (`rangeErrΨ_of_ifc`, `KVService.lean:1032`) | turns it into `rangeErrOut` (`KVService.lean:1021`) |
| exported `client_range_any` | `client/v3/Results.lean:2865` (post `rangeErrOut ms c F … err`, :2884) | exported text |
| (a) `ClientPutGet.lean:298`, `examples/etcd/txnlin/Calls.lean:344`, `k8s etcd3 watchChan__syncPaginated.lean:108` | | **drop it** (`⟨-, Hout, -⟩`): unaffected (B-i changes only the text they ignore) |
| (b) k8s `Client.Get` | `client/v3/kubernetes/Client__Get.lean:227-246` | **consumes** the future half into `k8s.rangeErrSound` (`kubernetes/Defs.lean:311`: `□ (⌜errDesc err = futureRevDesc⌝ -∗ …)`) |
| (b) k8s `Client.List` | `kubernetes/Client__List.lean:228` | the same |
| `Client.Get.latest` | `kubernetes/GetLatest.lean:42` | **drops** `rangeErrSound` (→ `store.Get`, `getCurrentState`, `GetCurrentResourceVersion`: unaffected) |
| `store.getList` | `k8s apiserver etcd3/store__getList.lean:141, 193` | passes `rangeErrSound` into `readErrIs` (`ListDefs.lean:369`, the same premise) |
| **`store.listReadError`** | `etcd3/store__listReadError.lean:56-66` | **the only place the premise is discharged**: `errors.Is(err, rpctypes.ErrFutureRev)` (k8s `store.go:922-934`), through the trusted `errors.IsStatusErr.spec` (`Spec/errors/IsStatusErr.lean`), post `b = true → errDesc err = errDesc target`, and `rpctypesInit`'s `errDesc eFR = futureRevDesc` |
| `store.pagedChunks` → `store.GetList` → k8s etcd3 closed theorems | `etcd3/store__pagedChunks.lean:338, 560`; `examples/k8s/etcd3/Adequacy.lean:133, 252, 344` (`k8s_etcd3_adequate`, `_cluster_adequate`, `_partition_adequate`) | |

**Does a comparison resolve B-i's `ctxErrMsg err` disjunct?** Only one consumer needs to, `listReadError`, and
it does in Go: `errors.Is(err, ErrFutureRev)` on a leaf error is `err == target || err.Is(target)`; a context
error (`*errors.errorString`, `context.deadlineExceededError`) has no `Is` method and a dynamic type other than
`EtcdError`, so `Is` returns false. But **the trusted post does not say so**: `IsStatusErr.spec` gives only
`b = true → errDesc err = errDesc target`. To use it, B-i needs either
- (i) `IsStatusErr.spec`'s post strengthened, for an `EtcdError` target, to `b = true → err.ty = EtcdError.ty`
  (or "`err` is not of a type in `ctxErrTys`") — a trusted-spec change; location-free (a type fact), so it is not
  exposed to `crossWorld` or to the persistent-auth fresh-world attack; or
- (ii) `rangeErrSound`/`readErrIs` restated as `□ (⌜errDesc err = futureRevDesc⌝ ∗ ⌜err.ty ∉ ctxErrTys⌝ -∗ …)`,
  with `listReadError` getting the type fact from (i) anyway.

So B-i closes with one more trusted-text change (i), and B5 shrinks to: `rangeErrΨ_of_ifc`/`rangeErrOut`
(client), `client_range_any`'s post text, `Client.Get`/`Client.List` and their specs, `rangeErrSound`, `readErrIs`,
`getList`, `listReadError`, `IsStatusErr.spec` (and its other users, which ignore the new conjunct). Estimate
100-150 lines instead of 100-400. R4 (a ghost-only consumer) does not occur.

**Findings on the way, for the Part B soundness note and the per-heap Scope.**
- `errors.IsStatusErr.spec`'s post `b = true → errDesc err = errDesc target` is a pure `errDesc` fact in the post
  of `errors.Is`, which is Perennial code with Lean semantics: Scope §0.2 (adequacy plus nondeterministic
  allocation) applies to it as to any pure `errDesc` post over interpreted code. Not new to this Scope, but in
  the same family; to be checked with Part B.
- `statusErrOk err` (`cache/v3/Base.lean:360`), which `IsStatusErr.spec` and `kClientErr` carry, is a
  persistent resource holding `errorMsgIs` (a WP form); the persistent-auth fresh-world attack must be run on
  every Part B text that concludes a pure fact from it.

### B.5 Steps and estimate

| step | lines |
|---|---|
| B0 inventory (read-only): every consumer of the KV error outcomes (`rangeErrΨ` and its siblings) up to the closed theorems; for each, whether a `FromError`/`ErrorDesc`/`==` resolves `ctxErrMsg` | report |
| B1 `descs` → `descDeadline`; the 50 `Hctx` users need no edit (instance field use only at the 3 sites) | ~20 |
| B2 `ctxErrDescs` restated, `Init.lean:296` from `toGRPCErrorMap_init`, `ServerKVOn` 820-826 | ~40 |
| B3 `ctxErrsErr`/`ctxErrClient` conjunct; producers `ErrorsNewOk:254-306`, `ChanCtx:166-219` (errorMsgIs proofs) | ~80 |
| B4 `waitRetryBackoff` proof; `ContextError.spec` and its proof; `ifcErrOut` and `_desc`/`_notin` | ~80 |
| B5 the KV outcomes (B-i) and their consumers, from B0 | 100-400 (unknown until B0) |
| B6 build, tcb (no axiom change; trusted text `ctxErrsErr`, premise `descs`), interfaces, STATUS, audit | ~40 |

Total: 3-6 days, mostly in B5.

### B.6 What changes in statements

- Closed theorems: only `Hctx`'s class loses a field, so the premise weakens. No text change.
- Exported (non-closed) client results: `client/v3/Results.lean` preconditions `ctxErrClient ci cd`. Same
  text, different meaning. The new form is satisfiable per run, so its callers' obligations get easier for
  real contexts. With B-i, the exported KV error outcomes change text (the `∨ ctxErrMsg err` disjunct).
  **Stop for review.**
- Trusted text: `ctxErrsErr` (grpc model), and the `ContextReadErrs` premise.

---

## Risks

- R1 (A): changing `srvRawStreamIs` (and `Incoming.lean`) rebuilds their importers. Measure with
  `etc/importers.py --count` first. The import already exists.
- R2 (B4): `status.Error`/`New`'s spec may not state `errDesc` of the result. Then `waitRetryBackoff` gets
  stuck the same way `ContextError` does (handle it as in B-i).
- R3 (B3): `deadlineExceededError.Error`'s WP may be unproved in Perennial. Then prove it locally (a lemma on
  translated code), not as an axiom.
- R4 (B5): B0 may find consumers that use `errDesc` with no `FromError` or type comparison (a ghost-only
  index). Then B-i does not close, and B-ii is needed. Stop at B0 with the inventory.
- R5 (both): the per-run reading of every remaining pure `incomingOf`/`errDesc` fact (§0, last paragraph) is
  not removed by this Scope. Only A-D (and its `errDesc` analogue) removes it.

## Open questions (each with a recommendation)

- **Q1.** Part A: A-C now, A-D later, or A-D now? Recommend **A-C now** (1 day; it removes the formal
  refutation and puts the two axioms at the same footing as `FromIncomingContext.spec`), and **A-D as its own
  Scope** after k8s 7f, together with the `errDesc` analogue (a per-heap `errDescIs`), since both share the
  model-level weakness.
- **Q2.** Where does `incomingKept` live: `srvRawStreamIs` (stream only) or `grpcRunCtx` (every run context)?
  Recommend **`srvRawStreamIs`**: one producer and one consumer, and no unary obligation.
- **Q3.** Keep `v3rpc.incomingOf_wrapper` as a named lemma or apply the axiom directly? Recommend **delete it**:
  it would be the axiom restated with nothing added.
- **Q4.** Part B direction: (A) per-run `ctxErrsErr` conjunct with B-i outcomes (recommended), B-ii (outcomes
  keyed by type), or keep the pure conjunct and add a premise (refused by the brief). Recommend **(A) + B-i,
  gated by B0**, a read-only inventory that reports before any Lean.
- **Q5.** Order: A and B are independent (disjoint files except `InvGrpc.lean`'s neighbourhood). Recommend
  **A first** (small, removes a refuted axiom), then B0, then B.
- **Q6.** The axiom names: keep `v3rpc.incomingOf_cancellableContext` (restated in place, per the no-twins
  rule) and delete `incomingOf_cancelCtx` (it becomes the definition `incomingKept`). Recommend as stated.
