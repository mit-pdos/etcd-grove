/-
**A `*cancelCtx` made by `context`** (k8s 7f-4, Addendum T-j, 2026-11-13; T-h5's option (A),
decided by etcd-grove-81): an opaque, persistent fact of a location, `context.madeCancelCtx c`, that
the weak context vocabulary `v3rpc.ctxDoneErr` (`SrvCtxWeak.lean`) states of the `*cancelCtx` a
context's `Value(&cancelCtxKey)` and `parentCancelCtx` find, in place of Perennial's `isCancelCtx`,
whose invariant (`cancelCtxInv`: a stored error is `Canceled`'s or `DeadlineExceeded`'s value) is false
of a `*timerCtx` made over etcd's require-leader wrapper once it is done (Addendum T-h1). TRUSTED: the
opaque and its law `context.madeCancelCtx_of_isCancelCtx` are part of the trust base. Lean-first.
-/
module

public import Perennial.Proof.context

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `madeCancelCtx`'s fact, raw (opaque). -/
opaque context.madeCancelCtxRaw (c : Loc) : IProp GF

/-- **The `*cancelCtx` at `c` was made by `context`** (persistent, opaque; TRUSTED; k8s 7f-4, Addendum
T-j): `c` was allocated by one of `context`'s constructors (`WithCancel`, `WithCancelCause`,
`WithDeadline(Cause)`, `WithTimeout(Cause)`: a `cancelCtx` alone, or the one embedded in a
`timerCtx`), and its fields (`mu`, `done`, `children`, `err`, `cause`, `Context`) are read and written
only by `context`'s code, under its own `mu` where `context` takes it. So, in Go, `context`'s
functions may use it as a parent: `parentCancelCtx` compares its `done` and locks its `mu`,
`propagateCancel` registers a child in its `children` or cancels the child with its `err`, and
`Cause` reads its `cause` under its `mu`, without a panic or a data race.

It says nothing of the errors `c` stores (unlike Perennial's `isCancelCtx`, whose invariant has
them be context errors): a `*timerCtx` made over a parent already done stores the parent's `Err()`,
which for etcd's require-leader wrapper is `rpctypes.ErrGRPCNoLeader` (Addendum T-h1,
`TestWithTimeoutWeak`).

What it excludes (Addendum T-h5): a value of type `*cancelCtx` that `context` did not make, which a
program can build with `reflect` (the type is unexported): a nil pointer (`parentCancelCtx` loads
its `done` through it: `TestRenewHTTPNilCancelCtxPanics`), or a non-nil copy of a real one (its own
`mu` over the real one's `children` map: a data race). A fresh zero value (`reflect.New`) is not
one either, although harmless in Go.

Given by: `context.madeCancelCtx_of_isCancelCtx` (every `isCancelCtx` is one), and the local axiom
`v3rpc.wp_WithTimeout_weak` (of the new `*timerCtx`'s embedded `cancelCtx`, through
`v3rpc.ctxChildErr`'s `"#HValue"` and `"#HParentCC"`). No other spec may give it. -/
def context.madeCancelCtx (c : Loc) : IProp GF := iprop(□ context.madeCancelCtxRaw c)

instance context.madeCancelCtx_persistent (c : Loc) :
    Persistent (context.madeCancelCtx (GF := GF) c) := by
  unfold context.madeCancelCtx; infer_instance

/-- **The result of `Value(&cancelCtxKey)`**, as `context.isCancelCtxAny` with `madeCancelCtx` in
place of `isCancelCtx` (persistent): if it is a `*cancelCtx`, `context` made it; `nil`, or a value of
another dynamic type, otherwise. -/
def context.madeCancelCtxAny (v : GoInterface) : IProp GF :=
  match v with
  | interface.ok ii =>
    if ii.ty = go.GoType.PointerType _root_.Perennial.context.cancelCtx.ty then
      iprop(∃ c : Loc, ⌜ii.v = #c⌝ ∗ context.madeCancelCtx c)
    else iprop(True)
  | interface.nil => iprop(True)

instance context.madeCancelCtxAny_persistent (v : GoInterface) :
    Persistent (context.madeCancelCtxAny (GF := GF) v) := by
  unfold context.madeCancelCtxAny
  split
  · split <;> infer_instance
  · infer_instance

end defs

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.context.Assumptions]

/-- (TRUSTED; k8s 7f-4, Addendum T-j) **Every `*cancelCtx` Perennial's model describes was made by
`context`**: `isCancelCtx c` (`Perennial/Proof/context/Base.lean`) is a `sync.isMutex` of `c`'s `mu`
whose lock invariant owns `c`'s `children` and `cause` fields, and an invariant owning its `done` and
`err` cells; Perennial's proofs establish it only of the locations `context`'s constructors allocate
(`wp_withCancel_`, the `timerCtx` of `wp_WithDeadlineCause`), the struct type `cancelCtx` is
unexported, and no spec of this repository or of Perennial gives a program a `cancelCtx`'s field
points-tos, so a verified program cannot build an `isCancelCtx` of a location `context` did not make.
In Go: a `reflect` copy shares the real one's `children` map, which the real one's lock invariant
owns (`ownMap`), so both cannot hold; a nil pointer has no fields. -/
axiom context.madeCancelCtx_of_isCancelCtx (c : Loc) :
    (_root_.Perennial.context.isCancelCtx c : IProp GF) ⊢ context.madeCancelCtx c

/-- `isCancelCtxAny ⊢ madeCancelCtxAny`, by `madeCancelCtx_of_isCancelCtx`. -/
theorem context.madeCancelCtxAny_of_isCancelCtxAny (v : GoInterface) :
    (_root_.Perennial.context.isCancelCtxAny v : IProp GF) ⊢ context.madeCancelCtxAny v := by
  unfold _root_.Perennial.context.isCancelCtxAny context.madeCancelCtxAny
  rcases v with ii | _
  · simp only
    split
    · iintro ⟨%c, %Hv, #Hc⟩
      iexists c
      isplitr
      · ipureintro; exact Hv
      iapply context.madeCancelCtx_of_isCancelCtx
      iexact Hc
    · iintro -; itrivial
  · iintro -; itrivial

end laws

end EtcdGrove
end Perennial
