/-
The proof of `Net/Spec/net/OpError__Timeout.lean`: `OpError.Timeout.impl`'s type assertions on
`Err` (`model.errFlag`), else the extension's `AnyBool`.
-/
module

public import Net.Spec.net.OpError__Timeout
public import Net.Proof.net.Errors

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions]
variable [go.BasicIntoValInj]

theorem errNetClosing_ty_ne_ptr (t : go.GoType) :
    internal.poll.errNetClosing.ty ≠ go.GoType.PointerType t := by
  unfold internal.poll.errNetClosing.ty; intro h; cases h

theorem deadline_ty_ne_timeout :
    go.GoType.PointerType internal.poll.DeadlineExceededError.ty ≠
      go.GoType.PointerType timeoutError.ty := by
  unfold internal.poll.DeadlineExceededError.ty timeoutError.ty; intro h; cases h

/-- `model.errFlag` of an `*OpError` whose `Err` is `e`: an answer `ErrFlag` allows. -/
theorem wp_errFlag (pe : Loc) (v : net.OpError) (Φ : val → IProp GF) :
    (pe ↦□ v : IProp GF) -∗ (∀ b, ⌜ErrFlag v.Err' b⌝ -∗ Φ #b) -∗
    WP (App (Val model.errFlag) (Val #pe)) {{ Φ }} := by
  iintro #Hpe HΦ
  unfold model.errFlag
  rw [OpError_ty_eq, timeoutError_ty_eq]
  ihave #H2 := Hpe
  iStructNamed H2
  wp_auto
  cases he : v.Err' with
  | nil =>
    wp_auto
    wp_bind (ExternalOp _ _ _)
    iapply wp_net_AnyBool
    iintro %b
    iapply HΦ
    ipureintro; trivial
  | ok ii =>
    dsimp only
    by_cases h1 : ii.ty = internal.poll.errNetClosing.ty
    · rw [decide_eq_true h1]
      wp_auto
      iapply HΦ
      ipureintro
      refine ⟨fun _ => rfl, fun h => absurd (h1.symm.trans h) (errNetClosing_ty_ne_ptr _),
        fun h => absurd (h1.symm.trans h) (errNetClosing_ty_ne_ptr _)⟩
    · rw [decide_eq_false h1]
      wp_auto
      by_cases h2 : ii.ty = go.GoType.PointerType internal.poll.DeadlineExceededError.ty
      · rw [decide_eq_true h2]
        wp_auto
        iapply HΦ
        ipureintro
        exact ⟨fun h => absurd h h1, fun _ => rfl, fun _ => rfl⟩
      · rw [decide_eq_false h2]
        wp_auto
        by_cases h3 : ii.ty = go.GoType.PointerType timeoutError.ty
        · rw [decide_eq_true h3]
          wp_auto
          iapply HΦ
          ipureintro
          exact ⟨fun h => absurd h h1, fun _ => rfl, fun _ => rfl⟩
        · rw [decide_eq_false h3]
          wp_auto
          wp_bind (ExternalOp _ _ _)
          iapply wp_net_AnyBool
          iintro %b
          iapply HΦ
          ipureintro
          exact ⟨fun h => absurd h h1, fun h => absurd h h2, fun h => absurd h h3⟩

theorem OpError.Timeout.wp_proof : OpError.Timeout.spec (GF := GF) (hG := hG) := by
  intro pe v
  wp_start as #Hpe
  (try wp_method_call)
  (try unfold OpError.Timeout.impl)
  (try wp_auto)
  wp_apply wp_errFlag pe v $$ Hpe as %b %hb
  iapply HΦ
  ipureintro; exact hb

end proof

end net
end Perennial
