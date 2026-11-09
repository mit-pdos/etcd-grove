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
`Background()` and `TODO()` (`ctxOk_background`, `TODO.spec`); the constructors `WithCancel`,
`WithTimeout` (a child: `ctxChild`, with `cancelOk`) and `WithValue` (`ctxWithValues`), `Done.spec`
and the Done channel's receive (`ctxDoneChan`, `doneRecv.spec`: a blocking receive or a `select`
case, Perennial's `recvAu`, completes only once the context is done). A context outside these (`WithValue`'s,
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
public import GeneratedProof.google_golang_org.grpc.metadata

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

/-- `TODO()` returns a context, never done: Perennial's `todoCtxVal` (named, so that a fact stated at
that value applies: 4b's `ctxTraceIs_todo`, `OtelTrace.ctxSpanOk_todo`). -/
def TODO.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.context }}
    (App (Val (@! context.TODO)) (Val #()))
  {{ (ctx : GoInterface), RET #ctx; ⌜ctx = GoInterface.ok context.todoCtxVal⌝ ∗ ctxOk ctx ∗
      □ (ctxDone ctx -∗ False) }}

/-- `Background()` is never done (its `Done()` is `nil`). -/
def ctxDone_background.spec : Prop :=
  ctxDone (GF := GF) (GoInterface.ok context.backgroundCtxVal) ⊢ iprop(False)

/-- `Background()` returns a context (the one `ctxOk_background` names). -/
def Background.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.context }}
    (App (Val (@! context.Background)) (Val #()))
  {{ (ctx : GoInterface), RET #ctx; ⌜ctx = GoInterface.ok context.backgroundCtxVal⌝ ∗ ctxOk ctx }}

/-- **`ctx'` is a child of `ctx`** (persistent): made by `WithCancel`, `WithTimeout` or
`WithDeadline` over `ctx`: it carries exactly `ctx`'s values (a request's metadata among them) and
is cancelled after `ctx` is (Go stores the parent's error before cancelling its children, so there
is a window where the parent is done and the child not yet: no law relates their `ctxDone`).
(`WithValue` adds a value: `ctxWithValues`, `ctxValueAt`.) -/
opaque ctxChild (ctx ctx' : GoInterface) : IProp GF := iprop(True)

def ctxChild_persistent.spec : Prop := ∀ ctx ctx', Persistent (ctxChild (GF := GF) ctx ctx')

/-- **A cancel function** (persistent): calling it makes `ctx` done. -/
def cancelOk (cancel : GoFunc) (ctx : GoInterface) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ (ctxDone ctx -∗ Φ #()) -∗
    WP (App (Val #cancel) (Val #())) {{ Φ }})

/-- **`WithCancel(parent)`** of any context: a child context and its cancel function. -/
def WithCancel.spec : Prop :=
  ∀ (parent : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ ctxOk parent }}
    (App (Val (@! context.WithCancel)) (Val #parent))
  {{ (ctx : GoInterface) (cancel : GoFunc), RET (PairV #ctx #cancel);
      ctxOk ctx ∗ ctxChild parent ctx ∗ cancelOk cancel ctx }}

/-- **`WithTimeout(parent, d)`** of any context: a child context, done by `d` at the latest (time
is not modelled: at some point), and its cancel function. -/
def WithTimeout.spec : Prop :=
  ∀ (parent : GoInterface) (d : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ ctxOk parent }}
    (App (App (Val (@! context.WithTimeout)) (Val #parent)) (Val #d))
  {{ (ctx : GoInterface) (cancel : GoFunc), RET (PairV #ctx #cancel);
      ctxOk ctx ∗ ctxChild parent ctx ∗ cancelOk cancel ctx }}

/-- **`ctx'` is `WithValue(ctx, key, _)`** (persistent): `ctx`'s values and one more, at `key`. -/
opaque ctxValueAt (ctx ctx' : GoInterface) (key : GoInterface) : IProp GF := iprop(True)

def ctxValueAt_persistent.spec : Prop := ∀ ctx ctx' key, Persistent (ctxValueAt (GF := GF) ctx ctx' key)

/-- **`WithValue(parent, key, val)`** of any context, for a non-nil key of a comparable type (Go
panics otherwise): a context carrying the value. -/
def WithValue.spec : Prop :=
  ∀ (parent v : GoInterface) (ki : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ ctxOk parent ∗
      ⌜⟦CheckComparable ki.ty, #()⟧ ⤳[under] #()⌝ }}
    (App (App (App (Val (@! context.WithValue)) (Val #parent)) (Val #(GoInterface.ok ki))) (Val #v))
  {{ (ctx : GoInterface), RET #ctx; ctxOk ctx ∗ ctxWithValues parent ctx ∗
      ctxValueAt parent ctx (GoInterface.ok ki) }}

/-- **`ctx` carries no gRPC outgoing metadata** (transparent, so that a batch owning a root context
can discharge it: net/http's request context, Kubernetes' `wait.ContextForChannel`): its
`Value(mdOutgoingKey{})` is `nil`, which is what grpc's `metadata.FromOutgoingContext` reads (the
key's type is unexported: only grpc's `metadata` package sets it). -/
def ctxNoMeta (ctx : GoInterface) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ Φ #GoInterface.nil -∗
    WP (App (Val (ctx @!! context.Context.ty @!! go!"Value"))
      (Val #(interface.mkOk google_golang_org.grpc.metadata.mdOutgoingKey.ty
        #(zero_val google_golang_org.grpc.metadata.mdOutgoingKey)))) {{ Φ }})

/-- `Background()` carries none. -/
def ctxNoMeta_background.spec : Prop :=
  ⊢ ctxNoMeta (GF := GF) (GoInterface.ok context.backgroundCtxVal)

/-- A child (`WithCancel`, `WithTimeout`) and a `WithValue` at another key keep it. -/
def ctxNoMeta_child.spec : Prop := ∀ ctx ctx',
  ctxNoMeta (GF := GF) ctx ∗ ctxChild ctx ctx' ⊢ ctxNoMeta ctx'

def ctxNoMeta_value.spec : Prop := ∀ (ctx ctx' : GoInterface) (ki : GoInterfaceOk),
  ctxNoMeta (GF := GF) ctx ∗ ctxValueAt ctx ctx' (GoInterface.ok ki) ∗
    ⌜ki.ty ≠ google_golang_org.grpc.metadata.mdOutgoingKey.ty⌝ ⊢ ctxNoMeta ctx'

/-- **`ctx`'s Done channel is `ch`** (persistent; `ch` not nil). -/
opaque ctxDoneChan (ctx : GoInterface) (ch : Loc) : IProp GF := iprop(True)

def ctxDoneChan_persistent.spec : Prop := ∀ ctx ch, Persistent (ctxDoneChan (GF := GF) ctx ch)

/-- **`ctx.Done()`**: `nil` for a context never done (`Background()`, `TODO()`, ...), else its Done
channel (the same one at every call). -/
def Done.spec : Prop :=
  ∀ (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ ctxOk ctx }}
    (App (Val (ctx @!! context.Context.ty @!! go!"Done")) (Val #()))
  {{ (ch : Loc), RET #ch; ⌜ch = null⌝ ∨ ctxDoneChan ctx ch }}

/-- **Receiving from a Done channel** (a blocking receive or a `select` case: Perennial's
`recvAu`): it completes only once the context is done. -/
def doneRecv.spec : Prop := ∀ (ctx : GoInterface) (ch : Loc),
  ctxDoneChan (GF := GF) ctx ch ⊢
    ∃ γc : ChanNames, isChan ch γc Unit ∗
      □ ∀ Φ : Unit → Bool → IProp GF, (∀ v ok, ctxDone ctx -∗ Φ v ok) -∗ recvAu γc Unit Φ

end ctx

end Context
end EtcdGrove
end Perennial
