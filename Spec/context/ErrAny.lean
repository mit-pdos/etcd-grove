/-
A context's `Err()`: Go's documented contract of `context.Context.Err` (the trust boundary).
Lean-first (no Rocq counterpart). Stated over Perennial's context model alone (2026-10-18).
-/
module

public import Perennial.Proof.context

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- `ctx.Err()` of any context (`context.isContext`): Go's documented contract of every
`Context` ("If Done is not yet closed, Err returns nil. If Done is closed, Err returns a non-nil
error explaining why: DeadlineExceeded if the context's deadline passed, or Canceled if the
context was canceled for some other reason"), which the standard contexts keep (a `cancelCtx`
stores `Canceled`, `DeadlineExceeded` or its parent's `Err()`). In the shape of `isContext`'s own
`Err` (`HErr`: at a known-done context, non-nil; otherwise `nil`, or the context is done), with
which error it is: `nil`, or the value of `context.Canceled` or of `context.DeadlineExceeded`;
and (2026-10-23, D37) what those two values are (Go's `context.go`: `var Canceled =
errors.New("context canceled")`, an `*errorString` whose `s` field nothing writes again;
`DeadlineExceeded error = deadlineExceededError{}`, a struct).
Perennial's `isContext` says only that a done context's error is typed (`isTypedErr`).
`context.ErrDone` (a done context's error is one of the two) follows (`ErrDone.lean`). -/
abbrev context.ErrAny.spec : Prop :=
  ∀ (c : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (cl : Broadcast),
  {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗ context.isContext c cd ∗
      (match cl with
       | .Done => context.ContextClosed cd.Done_gn
       | _ => iprop(True)) }}
    (App (Val #(methods c.ty go!"Err" c.v)) (Val #()))
  {{ (err : GoInterface), RET #err;
      (match cl with
       | .Done => iprop(⌜err ≠ interface.nil⌝)
       | _ => if err = interface.nil then iprop(True)
              else context.ContextClosed cd.Done_gn) ∗
      (⌜err = interface.nil⌝ ∨ ⌜context.isTypedErr err⌝ ∗
        -- (2026-10-23, D37) `Canceled` is `errors.New("context canceled")`, its cell holding the
        -- message for good; `DeadlineExceeded` is a `deadlineExceededError{}`, no `*errorString`
        ((globalAddr context.Canceled ↦□ err ∗ ∃ x : Loc,
            ⌜err = interface.mkOk
              (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x⌝ ∗
            x.[_root_.Perennial.errors.errorString, go!"s"] ↦□ go!"context canceled") ∨
          (globalAddr context.DeadlineExceeded ↦□ err ∗ ⌜∀ x : Loc, err ≠ interface.mkOk
              (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x⌝))) }}

end spec

end EtcdGrove
end Perennial
