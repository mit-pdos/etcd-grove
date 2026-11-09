/-
# Any Go context (batch W0: the ambient context)

Perennial's `context` proofs (`Perennial.Proof.context`) cover the contexts its constructors make
(`isContext`: a `*cancelCtx` or a `*timerCtx`), not `Background()` (its `Done()` is `nil`), not a
context made by `WithValue` (grpc's metadata, `WithRequireLeader`), nor one a caller builds (the
Kubernetes store's `wait.ContextForChannel`). The client's API takes whatever context its callers
pass, so it is stated over **one bundle predicate**, the contract of `context.Context`'s methods
that the client's code relies on (PRINCIPLES, "an interface value gets a bundle"):

* `ctxOk ctx` (persistent): `ctx` is a non-nil `context.Context` whose methods meet Go's documented
  contract: `Err()` returns `nil`, or `Canceled`'s or `DeadlineExceeded`'s value once the context is
  done, and then the same kind of value on every later call; `Done()` returns a channel closed once
  the context is done, or `nil` for a context never done; `Value(k)` returns what the context chain
  holds at `k` (whatever: the client's code only passes it on, to grpc's metadata).
* `ctxDone ctx` (persistent): `ctx` is done (`Err()` is not `nil`, and never will be again).

Laws (obligations of whoever realizes the bundle, from Perennial's specs and each context's
code): `Err.spec`, `ErrDone.spec`; introduction from Perennial's contexts (`ctxOk_of_isContext`),
`Background()` and `TODO()` (`ctxOk_background`, `ctxOk_todo`). A context outside these (`WithValue`'s,
a caller's own type) is introduced by the spec of the function that makes it (`WithRequireLeader`,
`client/v3/ctx.go`; Kubernetes' contexts, batch 1g's users), never by unfolding.

Intended realization: `ctxOk ctx := □ (the triples of Err, Done, Value at ctx)` with `ctxDone`
the done flag of Perennial's descriptor (`ContextClosed`) or a context-specific one; the
realization is per context type, so the predicate is opaque.

Who calls what: the client's `ContextError` calls `Err()` (twice: `ErrDone.spec` is what keeps
its result non-nil); everything else the client does with a context is to pass it to gRPC
(`req/google_golang_org_grpc.md`, which takes `ctxOk`).
-/
module

public import Perennial.Proof.context

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Context

open Iris Iris.BI

section ctx
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **`ctx` is a Go context** meeting `context.Context`'s contract (persistent; see the header). -/
opaque ctxOk (ctx : GoInterface) : IProp GF := iprop(True)

/-- **`ctx` is done** (persistent). -/
opaque ctxDone (ctx : GoInterface) : IProp GF := iprop(True)

/-- **`ctx'` is `ctx` with values added** (persistent): a `WithValue` chain over `ctx` (grpc's
outgoing metadata, `WithRequireLeader`): done exactly when `ctx` is. -/
opaque ctxWithValues (ctx ctx' : GoInterface) : IProp GF := iprop(True)

def ctxWithValues_persistent.spec : Prop := ∀ ctx ctx', Persistent (ctxWithValues (GF := GF) ctx ctx')

/-- Done together. -/
def ctxWithValues_done.spec : Prop := ∀ ctx ctx',
  ctxWithValues (GF := GF) ctx ctx' ⊢ □ (ctxDone ctx ∗-∗ ctxDone ctx')

def ctxOk_persistent.spec : Prop := ∀ ctx, Persistent (ctxOk (GF := GF) ctx)
def ctxDone_persistent.spec : Prop := ∀ ctx, Persistent (ctxDone (GF := GF) ctx)

/-- A context is not `nil`. -/
def ctxOk_ne_nil.spec : Prop := ∀ ctx, ctxOk (GF := GF) ctx ⊢ ⌜ctx ≠ GoInterface.nil⌝

/-- **`ctx.Err()`**: `nil`, or (the context done) `Canceled`'s or `DeadlineExceeded`'s value. -/
def Err.spec : Prop :=
  ∀ (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ ctxOk ctx }}
    (App (Val (ctx @!! context.Context.ty @!! go!"Err")) (Val #()))
  {{ (err : GoInterface), RET #err;
      ⌜err = GoInterface.nil⌝ ∨ (ctxDone ctx ∗ context.isCtxErr err) }}

/-- **`ctx.Err()` once the context is done**: not `nil` (Go's contract: "After Err returns a
non-nil error, successive calls to Err return the same error"). -/
def ErrDone.spec : Prop :=
  ∀ (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ ctxOk ctx ∗ ctxDone ctx }}
    (App (Val (ctx @!! context.Context.ty @!! go!"Err")) (Val #()))
  {{ (err : GoInterface), RET #err; ⌜err ≠ GoInterface.nil⌝ ∗ context.isCtxErr err }}

/-- Perennial's contexts are contexts. -/
def ctxOk_of_isContext.spec : Prop :=
  ∀ (c : GoInterfaceOk) (s : context.ContextDesc (IProp GF)),
  context.isContext c s ⊢ ctxOk (GoInterface.ok c)

/-- `Background()` is a context (never done). -/
def ctxOk_background.spec : Prop :=
  ⊢ ctxOk (GF := GF) (GoInterface.ok context.backgroundCtxVal)

/-- `TODO()` returns a context. -/
def TODO.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.context }}
    (App (Val (@! context.TODO)) (Val #()))
  {{ (ctx : GoInterface), RET #ctx; ctxOk ctx }}

/-- `Background()` returns a context (the one `ctxOk_background` names). -/
def Background.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.context }}
    (App (Val (@! context.Background)) (Val #()))
  {{ (ctx : GoInterface), RET #ctx; ctxOk ctx }}

end ctx

end Context
end EtcdGrove
end Perennial
