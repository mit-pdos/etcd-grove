# incomingof Part A: the incoming-metadata links, restated per run (2026-11-17)

Branch `incomingof-scope` (worktree `/shared/etcd-grove-incomingof`), the incomingof agent of
etcd-grove-03. Approved by the user 2026-11-17 via etcd-grove-03 (`notes/incomingof-scope.md`, Part A,
option A-C variant C-ii; Q2: the law in `srvRawStreamIs`; Q3: no `incomingOf_wrapper`; Q6: the v3rpc
axiom restated in place under its name, `incomingOf_cancelCtx` deleted). This file holds the exact
final texts and the argument, for the independent attack before the change is linked.

## What it repairs

`EtcdGrove.incomingOf_cancelCtx` (`ctxField c ↦□ p ⊢ ⌜incomingOf (*cancelCtx c) = incomingOf p⌝`) and
`v3rpc.incomingOf_cancellableContext` (`ccField l ↦□ c ⊢ ⌜incomingOf (ccCtx l) = incomingOf c⌝`) are
false in meaning: their antecedent is a bare persistent points-to, which `crossWorld` builds in a fresh
heap at any address with any content, so `incomingOf` is constant (`incomingOf_const`, proved on branch
`axiom/ctx-descs`; `notes/axiom-review/ctx-descs.md`; bug record `notes/incomingof-crossworld.md`).
Go disagrees (`TestIncomingNotConstant`, below).

## The final texts

### 1. Deleted

- `axiom EtcdGrove.incomingOf_cancelCtx` and its corollary `incomingOf_cancelCtx_parent_unique`
  (`Proof/google_golang_org/grpc/metadata/Incoming.lean`).
- `v3rpc.incomingOf_cancellableContext_field_unique` and `v3rpc.incomingOf_wrapper` (proved;
  `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/WrapperMd.lean`): the interceptor applies the
  restated axiom directly (Q3).

### 2. New definition (not trusted by itself: it is trusted only where a trusted text delivers it)

`Proof/google_golang_org/grpc/metadata/Incoming.lean:58`:

```lean
def metadata.incomingKept (ci : GoInterfaceOk) : IProp GF :=
  iprop(□ ∀ c : Loc, _root_.Perennial.context.ctxField c ↦□ (GoInterface.ok ci) -∗
    ⌜metadata.incomingOf (GoInterface.ok (interface.mk
        (go.GoType.PointerType _root_.Perennial.context.cancelCtx.ty) #c)) =
      metadata.incomingOf (GoInterface.ok ci)⌝)

instance metadata.incomingKept_persistent (ci : GoInterfaceOk) :
    Persistent (metadata.incomingKept (GF := GF) ci)
```

No law about it is proved or assumed: nothing produces it but item 3, nothing consumes it but item 4.

### 3. Trusted text changed: `srvRawStreamIs` gains a conjunct

`Proof/google_golang_org/grpc/InvGrpcStream.lean:452` (the raw server end grpc's model delivers in
`grpcAccepted`, the post of the model-only `acceptRun`/`acceptRunConns`). Old last line:

```lean
    context.isContext ci cd ∗ grpcRunCtx ci ∗ context.libCtxOkC ci ∗ trace.spanCtxOkC ci ∗
    http.netCtxOkC ci)
```

New:

```lean
    context.isContext ci cd ∗ grpcRunCtx ci ∗ context.libCtxOkC ci ∗ trace.spanCtxOkC ci ∗
    http.netCtxOkC ci ∗ metadata.incomingKept ci)
```

Docstring sentence added: "A `*cancelCtx` whose `Context` field holds `ci` has `ci`'s incoming
metadata (`metadata.incomingKept ci`): `FromIncomingContext` reads it through `Value(mdIncomingKey{})`,
which a `*cancelCtx` answers as its parent does."

Other trusted texts that mention `srvRawStreamIs` now claim the conjunct too, with the same `ci`:
`srvStreamInterceptorOk` (grpc-prometheus's stream interceptor axiom passes its handler a raw end
`st'` "with the same context `ci`"), which is what grpc-prometheus does (`monitoredServerStream`'s
`Context()` is `ss.Context()`), so the conjunct is the same fact of the same `ci`.

### 4. Trusted text restated: `v3rpc.incomingOf_cancellableContext` (same name)

`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/WrapperMd.lean:83`. Old:

```lean
axiom v3rpc.incomingOf_cancellableContext (l : Loc) (c : GoInterfaceOk) :
    (v3rpc.ccField l ↦□ (GoInterface.ok c) : IProp GF) ⊢ (iprop(⌜metadata.incomingOf
      (GoInterface.ok (v3rpc.ccCtx l)) = metadata.incomingOf (GoInterface.ok c)⌝) : IProp GF)
```

New:

```lean
axiom v3rpc.incomingOf_cancellableContext (l c : Loc) (ci : GoInterfaceOk) :
    (metadata.incomingKept ci ∗ _root_.Perennial.context.ctxField c ↦□ (GoInterface.ok ci) ∗
      v3rpc.ccField l ↦□ (GoInterface.ok (interface.mk
        (go.GoType.PointerType _root_.Perennial.context.cancelCtx.ty) #c)) : IProp GF) ⊢
    (iprop(⌜metadata.incomingOf (GoInterface.ok (v3rpc.ccCtx l)) =
      metadata.incomingOf (GoInterface.ok ci)⌝) : IProp GF)
```

where `v3rpc.ccField l = structFieldRef v3rpc.cancellableContext "Context" l` and `v3rpc.ccCtx l =
interface.mk (PointerType v3rpc.cancellableContext.ty) #l`.

Its only use: `newStreamInterceptor.lean`, where `Hkept` comes from the run's `srvRawStreamIs`,
`Hcf : ctxField c ↦□ ci` from `v3rpc.wp_WithCancel_cancelCtx` (proved), and `Hfield : ccField l ↦□
cancelCtx c` from `newCancellableContext`'s proof (`ccHandle`). The conclusion feeds the handler
hypothesis `Hk` at `incomingOf ci` (unchanged).

## Why it is true, in Go

- `(*cancelCtx).Value(key)` is `if key == &cancelCtxKey { return c }; return value(c.Context, key)`
  (go1.27.3 `src/context/context.go:442-447`), and `value` walks `*valueCtx`/`*cancelCtx`/`*timerCtx`/
  `withoutCancelCtx` by their fields and calls `Value` otherwise (`:776-807`). For `mdIncomingKey{}`
  (not `&cancelCtxKey`), a `*cancelCtx` answers as the value of its `Context` field.
- `WithCancel(ci)` writes the field in `propagateCancel` (`:477`, `c.Context = parent`) before
  returning; the `afterFuncer` branch (`:514`) rewrites it to `stopCtx{Context: parent, ...}`, after
  which the cell no longer holds `ci` (no persistent points-to at `ci` survives), and a `stopCtx`
  answers `Value` through its embedded `parent` anyway.
- `type cancellableContext struct { context.Context; lock sync.RWMutex; cancel context.CancelFunc;
  cancelReason error }` (fork `673da07c8f` `server/etcdserver/api/v3rpc/interceptor.go:270-276`)
  overrides only `Err` and adds `Cancel`; `Value` is promoted, `l.Context.Value(key)`.
- `metadata.FromIncomingContext(x)` (grpc v1.84.0 `metadata/metadata.go:268-282`) is a function of
  `x.Value(mdIncomingKey{})`.

So the wrapper `l` over `c` over `ci` answers `FromIncomingContext` as `ci` does. Neither law reads a
field other than the one in its antecedent, so it holds even if the cell is read as part of a value
of another type (see attack 6).

Go evidence: `examples/axiomcx/incomingof/md_test.go` (own module, grpc v1.84.0; run with
`GOTOOLCHAIN=go1.27.3 GOWORK=off go test -v ./...` in that directory, 2026-11-17, all pass):

```
=== RUN   TestWrapperInheritsIncoming
    md_test.go:50: token tokA: WithCancel child and wrapper carry it
    md_test.go:50: token tokB: WithCancel child and wrapper carry it
--- PASS: TestWrapperInheritsIncoming (0.00s)
=== RUN   TestIncomingNotConstant
    md_test.go:66: cancelCtx over md: ok=true; over Background: ok=false
--- PASS: TestIncomingNotConstant (0.00s)
```

`TestWrapperInheritsIncoming`: for two tokens, the `*cancelCtx` over `NewIncomingContext(..., tok)`
and etcd's `cancellableContext` shape over it both return `tok`. `TestIncomingNotConstant`: two
`*cancelCtx`s of one run answer differently, which refutes the old axiom's consequence
`incomingOf_const`. (The file's two other tests, `TestCtxErrDescs` and `TestErrorStringDescByCell`,
are Part B's evidence.)

## The cross-world check and the other attacks

1. **`crossWorld` (the refutation of the old texts).** It needs an antecedent made of bare persistent
   points-tos (or WP forms over proved code), which it builds at a fresh heap name. The new axiom's
   antecedent has `metadata.incomingKept ci`, a persistent wand whose conclusion is a pure fact about
   the opaque `incomingOf`; building it means proving `∀ c, ... ⌜incomingOf (*cancelCtx c) =
   incomingOf ci⌝`, which nothing in Lean or the trust base gives except item 3. Item 3 is the post of
   `acceptRun`/`acceptRunConns`, model-only names with no body in the semantics' function table
   (`TrustedCode/google_golang_org/grpc.lean:47-53`): their triples are their whole semantics, and a
   model in which they diverge satisfies them, so no adequacy argument turns their posts into Lean
   facts, at the run's heap name or at a fresh one (the same reason the ctx-descs review's step 2
   failed for `toGRPCErrorMap_init`). The two points-tos alone conclude nothing.
2. **Adequacy plus nondeterministic allocation (Scope §0.2).** The law is not in the post of code with
   Lean semantics (`WithCancel`, `newCancellableContext`): those posts carry only points-tos
   (`v3rpc.wp_WithCancel_cancelCtx`, proved, unchanged). So two closed runs that allocate at the same
   address over different parents export no `incomingOf` equation.
3. **A looping `Value` (the T-b attack).** No law takes a `Value` WP (`ctxValueFrom`, `valueAt`); the
   links are a `*cancelCtx`'s `Context` cell and a `*cancellableContext`'s `Context` cell, each with
   exactly one value (two persistent points-tos of a cell agree). A context `L` whose `Value` loops
   satisfies no such cell unless a real `*cancelCtx` was built over it, and then only with `L` as its
   one parent; `incomingKept L` would have to come from grpc's delivery of `L` as a run context.
4. **Two streams of one run** (run contexts `ci1`, `ci2`, different metadata, both `incomingKept`).
   Deriving `incomingOf ci1 = incomingOf ci2` in the logic needs a `c` with `ctxField c ↦□ ci1` and
   `↦□ ci2`, which agreement refutes. Inside a proof, a fresh `c` needs an allocation, which happens at
   the authoritative heap of the run and returns one value per cell.
5. **The all-resources reading** (Scope §0, last paragraph; Q1). In the model, `incomingKept ci1 ∗
   incomingKept ci2` at some resource is only satisfiable if `incomingOf ci1 = incomingOf ci2` (extend
   by a fragment for an unowned `c`). This is not derivable by a WP proof (only entailments are, and a
   fragment for a fresh cell needs the authoritative heap), and it is the same per-run reading the
   repository accepts for `FromIncomingContext.spec`'s, `WithValue.spec`'s and `Tracer.Start.spec`'s
   `incomingOf` posts. It would make two run contexts with different metadata in one run inconsistent
   in the model, so the posts claiming those metadata would be unsatisfiable together in the model;
   since only the uninterpreted `acceptRun` delivers both, no closed theorem extracts a falsehood. The
   fully sound fix is the per-heap IProp `incomingIs` (Scope A-D, Q1: its own Scope later).
6. **Type confusion of cells.** `structFieldRef` is an offset (`Perennial/.../unsafememory/Layout.lean`:
   `structFieldRef_offset`), and `Context` is the first field of both `cancelCtx` and
   `cancellableContext`, so any interface-typed cell the program owns at `c` gives `ctxField c ↦□ ci`.
   The conclusion is then about `(*cancelCtx)(c)`, a value no Go code outside `context` can make
   without `unsafe`, so no `FromIncomingContext.spec` post exists about it; and the law reads only
   that one cell, so the conclusion would hold of the reinterpreted memory too. Same for `ccField l`.
7. **The `afterFuncer` rewrite.** A persistent points-to at `ci` excludes it (the cell would change).
8. **Vacuity of `incomingKept`.** Could a proof build it because `ctxField c ↦□ ci` is unsatisfiable
   for some `ci`? A persistent points-to of any interface value is satisfiable (a fresh fragment), so
   no `ci` makes the wand trivial.

Not tried: a Lean formalization of attack 5 (it needs an Iris model argument, not a proof inside the
logic); a counterexample program (the repository's `axiom` skill form), since the texts are a
restatement that no closed theorem's statement mentions.

## Trust-base delta (expected; checked after the build)

- `etc/tcb-baseline.txt`: `axiom incomingOf_cancelCtx` removed; `axiom
  v3rpc.incomingOf_cancellableContext` kept (restated).
- The 22 collections that listed both (auth3, authN, authkv, cachekv, compactkv, k8scompactor,
  k8setcd3, leaseN, leasecatchup, leaseexpiry, leaseexpiryN, leasekv, linkv3p, linkvtxn, m2, putget,
  putget3, putgetN, txnlinfaultsN, v3rpc, watch, watchkv) each lose the one line.
- Trusted text changed: `srvRawStreamIs` (one conjunct). No closed statement's text changes (no
  `Results`/`Adequacy` statement mentions `incomingOf` or `srvRawStreamIs`).

## Verdict

Pending the independent attack (etcd-grove-03).
