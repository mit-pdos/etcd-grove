/-
What clockwork's initializer (`Init.lean`, `etc/gen-init.py`) needs beyond the specs it calls:
`context.DeadlineExceeded`'s value (`deadlineExceededError{}`) is an error `fmt` formats by its
`Error()` (`errOk`), the argument of `ErrFakeClockDeadlineExceeded`'s `fmt.Errorf("...: %w", ...)`
(`fmt.ErrorfErrs.wp_proof`). Lean-first (prove-b64clock, 2026-11-20).
-/
module

public import Spec.fmt.ErrorfErrs
public import Perennial.Proof.context.NewErrorString

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace clockwork

open Iris Iris.BI Iris.ProofMode

section facts
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [context.Assumptions]

/-- `deadlineExceededError{}` has `Error() string` and no `Format`, and its `Error()` returns. -/
theorem errOk_deadlineExceeded (ii : GoInterfaceOk)
    (h : GoInterface.ok ii = interface.mkOk _root_.Perennial.context.deadlineExceededError.ty
      #(zero_val _root_.Perennial.context.deadlineExceededError)) :
    ⊢ errOk (GF := GF) ii := by
  rw [interface.mkOk] at h; cases h
  unfold errOk
  isplit
  · ipureintro
    have h1 := (go.MethodSetIs.method_set_is
      (t := _root_.Perennial.context.deadlineExceededError.ty) go!"Format")
    have h2 := (go.MethodSetIs.method_set_is
      (t := _root_.Perennial.context.deadlineExceededError.ty) go!"Error")
    simp only [go.methodSetLookup] at h1 h2
    exact ⟨by simpa using h1, by simpa [EtcdGrove.noArgStringSig] using h2⟩
  · imodintro
    iintro %Φ HΦ
    wp_method_call
    unfold _root_.Perennial.context.deadlineExceededError.Error.impl
    wp_auto
    iapply HΦ

/-- `ErrFakeClockDeadlineExceeded`'s `fmt.Errorf` format and argument are ones `fmt.ErrorfErrs` takes. -/
theorem errArgsWf_fakeClock (ii : GoInterfaceOk) :
    fmt.errArgsWf [ii] go!"clockwork.FakeClock: %w" [GoInterface.ok ii] :=
  fmt.errArgsWf_intro (ds := [⟨W8 119, false⟩]) (by decide) (by rfl)
    ⟨Or.inr ⟨List.mem_singleton_self _, by decide, rfl⟩, trivial⟩

end facts

end clockwork
end EtcdGrove
end Perennial
