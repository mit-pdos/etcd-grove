/-
Access to the generation's crash token `notCrashed` (`Perennial/GooseLang/CrashToken.lean`) before a
step. The token is part of the bounded language's state interpretation (`gooseBstateInterp`), so a
thread can use it only at a step; these lemmas give the fancy update before a step of a non-value
expression the token, which it must hand back (it is exclusive: the update may use it, for
instance to rule out the crash branch of an invariant with `notCrashed_crashed`, but not keep it).

* `wp_notCrashed_acc`: any non-value expression, mask unchanged (as Perennial's `wp_ext_acc`).
* `wp_atomic_nc`: `wp_atomic` whose mask-changing update before the step gets the token: the
  update opening an atomic update around an atomic step (`LinuxFs/Proof/os/SharedAu.lean`,
  `wp_aunc_step`).

Proved here over Perennial's definitions (untrusted); a general lemma for Perennial's
`GooseLang/Lifting.lean` (`notes/perennial-changes.md`, "notCrashed before a step").
-/
module

public import Perennial.GooseLang.Lifting

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section nc
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- **The crash token before a step**: the update before the step of a non-value `e` may use the
generation's `notCrashed`, and gives it back. -/
theorem wp_notCrashed_acc (e : Expr) (Φ : val → IProp GF) (h : toVal e = none) :
    (notCrashed -∗ |={E}=> notCrashed ∗ WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }} := by
  have h' : ToVal.toVal (Val := val) e = none := h
  iintro Hacc
  iapply wp_unfold.2
  unfold wp.pre
  rw [h']
  dsimp only
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  rcases σ₁ with ⟨σ₁, c⟩
  icases (goose_bstateInterp_eq σ₁ c ns (obs ++ obs') nt).1 $$ Hσ with ⟨Hσ, Hc, Ht, Hnc⟩
  imod Hacc $$ Hnc with ⟨Hnc, Hwp⟩
  ihave Hwp := wp_unfold.1 $$ Hwp
  unfold wp.pre
  rw [h']
  dsimp only
  iapply Hwp $$ %(σ₁, c) %ns %obs %obs' %nt
  iapply (goose_bstateInterp_eq σ₁ c _ _ _).2
  iframe

/-- **`wp_atomic` with the crash token**: the mask-changing update before the atomic step of a
non-value `e` may use the generation's `notCrashed`, and gives it back. -/
theorem wp_atomic_nc {E1 E2 : CoPset} (e : Expr) (Φ : val → IProp GF) (h : toVal e = none)
    [ι : Language.Atomic ↑s e] :
    (notCrashed -∗ |={E1,E2}=> notCrashed ∗ WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢
      WP e @ s; E1 {{ Φ }} := by
  have h' : ToVal.toVal (Val := val) e = none := h
  iintro H
  iapply wp_unfold.2
  unfold wp.pre
  rw [h']
  dsimp only
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  rcases σ₁ with ⟨σ₁, c⟩
  icases (goose_bstateInterp_eq σ₁ c ns (obs ++ obs') nt).1 $$ Hσ with ⟨Hσ, Hc, Ht, Hnc⟩
  imod H $$ Hnc with ⟨Hnc, H⟩
  ihave Hσ : stateInterp (GF := GF) ((σ₁, c) : BcfgState) ns (obs ++ obs') nt $$ [Hσ Hc Ht Hnc]
  · iapply (goose_bstateInterp_eq σ₁ c _ _ _).2
    iframe
  ihave H := wp_unfold.1 $$ H
  unfold wp.pre
  rw [h']
  dsimp only
  imod H $$ Hσ with ⟨$, H⟩
  imodintro
  iintro %e2 %σ2 %efs %Hstep Hcred
  ihave aux := H $$ %e2 %σ2 %efs %Hstep Hcred
  iapply step_fupdN_wand $$ aux
  iintro >(⟨Hσ, H, Hefs⟩)
  irevert %ι
  match s with
  | .NotStuck =>
    simp only [wp_unfold.to_eq]
    dsimp only [wp.pre]
    match h₂ : ProgramLogic.toVal e2 with
    | some v2 =>
      iintro %ι
      icases H with > > $
      iframe
    | none =>
      iintro %ι
      icases H $$ %σ2 %(ns + 1) %([]) %_ %(nt + efs.length) [Hσ] with >⟨%h, _⟩
      · exact .rfl
      exact ((Language.not_reducible_iff_irreducible.mpr (ι.atomic Hstep)) h).elim
  | .MaybeStuck =>
    iintro %ι
    have ⟨v, h⟩ := Option.isSome_iff_exists.mp (ι.atomic Hstep)
    obtain ⟨rfl⟩ := (ToVal.coe_of_toVal_eq_some h)
    simp only [wp_value_fupd'.to_eq]
    imod H with > H
    iframe

end nc

end Perennial
