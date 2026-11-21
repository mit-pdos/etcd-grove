/-
**The crash-token update** (`ncfupd`, Rocq Perennial's `ncfupd`): a fancy update that may use the
generation's `notCrashed` (`Perennial/GooseLang/CrashToken.lean`), and gives it back. The token is
part of the bounded language's state interpretation, so a thread can use it only at a step: before
one (`wp_ncfupd`, from `wp_notCrashed_acc`), or after its last one, in the postcondition of an
expression that takes at least one step (`wp_ncfupd_post`).

`notes/raft-crash-law-design.md` (i): raft's ghost steps take the token (a crash may change state
they update or read: the leader-side authorities and the slot's half of the virtual maps live in
the crash invariant), and a function whose ghost step runs at its return (`raft.Step`'s arms) gets it
by `wp_ncfupd_post`.

Proved here over Perennial's definitions (untrusted); a general change for Perennial's
`GooseLang/Lifting.lean` (`notes/perennial-changes.md`, "notCrashed before a step").
-/
module

public import GooseLang.Ext.Fs.NotCrashedAcc

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section nc
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- **The crash-token update at `E`**: an update at `E` given the generation's `notCrashed`, which
it gives back. -/
def ncfupd (E : CoPset) (P : IProp GF) : IProp GF :=
  iprop(notCrashed -∗ |={E}=> notCrashed ∗ P)

theorem ncfupd_intro {E : CoPset} {P : IProp GF} : (|={E}=> P) ⊢ ncfupd E P := by
  unfold ncfupd
  iintro H Hnc
  imod H
  imodintro
  iframe

theorem ncfupd_ret {E : CoPset} {P : IProp GF} : P ⊢ ncfupd E P := by
  unfold ncfupd
  iintro H Hnc
  imodintro
  iframe

theorem ncfupd_trans {E : CoPset} {P : IProp GF} : ncfupd E (ncfupd E P) ⊢ ncfupd E P := by
  unfold ncfupd
  iintro H Hnc
  imod H $$ Hnc with ⟨Hnc, H⟩
  iapply H $$ Hnc

theorem ncfupd_wand {E : CoPset} {P Q : IProp GF} : ncfupd E P ∗ (P -∗ Q) ⊢ ncfupd E Q := by
  unfold ncfupd
  iintro ⟨H, HW⟩ Hnc
  imod H $$ Hnc with ⟨Hnc, H⟩
  imodintro
  iframe Hnc
  iapply HW $$ H

/-- An update between two crash-token updates. -/
theorem ncfupd_fupd {E : CoPset} {P : IProp GF} : (|={E}=> ncfupd E P) ⊢ ncfupd E P := by
  unfold ncfupd
  iintro H Hnc
  imod H
  iapply H $$ Hnc

/-- A crash-token update after one, then into a third (the bind). -/
theorem ncfupd_bind {E : CoPset} {P Q : IProp GF} : ncfupd E P ∗ (P -∗ ncfupd E Q) ⊢ ncfupd E Q :=
  ncfupd_wand.trans ncfupd_trans

/-- **A crash-token update before a step** of a non-value `e` (`wp_notCrashed_acc`). -/
theorem wp_ncfupd {s : Stuckness} {E : CoPset} (e : Expr) (Φ : val → IProp GF) (h : toVal e = none) :
    ncfupd E (WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }} := by
  unfold ncfupd
  exact wp_notCrashed_acc e Φ h

/-- (Löb's body) The postcondition's crash-token update, run at the last step: by the state
interpretation that step holds. -/
private theorem wp_ncfupd_post_step {s : Stuckness} {E : CoPset} (σ : BcfgState) (ns : Nat)
    (κs : List Observation) (nt : Nat) (e : Expr) (Φ : val → IProp GF) :
    ⊢ □ (∀ e Φ, ⌜toVal e = none⌝ -∗ WP e @ s; E {{ v, ncfupd E (Φ v) }} -∗ WP e @ s; E {{ Φ }}) -∗
      stateInterp (GF := GF) σ ns κs nt -∗ WP e @ s; E {{ v, ncfupd E (Φ v) }} ={E}=∗
      stateInterp (GF := GF) σ ns κs nt ∗ WP e @ s; E {{ Φ }} := by
  iintro #IH Hσ H
  match h : ProgramLogic.toVal e with
  | some v =>
    obtain ⟨rfl⟩ := ToVal.coe_of_toVal_eq_some h
    rcases σ with ⟨σ, c⟩
    icases (goose_bstateInterp_eq σ c ns κs nt).1 $$ Hσ with ⟨Hσ, Hc, Ht, Hnc⟩
    ihave H := wp_value_fupd'.1 $$ H
    imod H with H
    unfold ncfupd
    imod H $$ Hnc with ⟨Hnc, HΦ⟩
    imodintro
    isplitl [Hσ Hc Ht Hnc]
    · iapply (goose_bstateInterp_eq σ c ns κs nt).2
      iframe
    iapply wp_value_fupd'.2
    imodintro
    iexact HΦ
  | none =>
    imodintro
    iframe Hσ
    iapply IH $$ %e %Φ %(h : toVal e = none) H

/-- **A crash-token update in the postcondition** of a non-value `e`: run after `e`'s last step, by
the state interpretation that step holds (the token is part of it). -/
theorem wp_ncfupd_post {s : Stuckness} {E : CoPset} (e : Expr) (Φ : val → IProp GF)
    (h : toVal e = none) :
    WP e @ s; E {{ v, ncfupd E (Φ v) }} ⊢ WP e @ s; E {{ Φ }} := by
  suffices H : ⊢ ∀ e Φ, ⌜toVal e = none⌝ -∗ WP e @ s; E {{ v, ncfupd E (Φ v) }} -∗
      WP e @ s; E {{ Φ }} by
    iintro Hwp
    iapply H $$ %e %Φ %h Hwp
  iloeb as IH
  iintro %e %Φ %h H
  have h' : ToVal.toVal (Val := val) e = none := h
  iapply wp_unfold.2
  ihave H := wp_unfold.1 $$ H
  unfold wp.pre
  rw [h']
  dsimp only
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  imod H $$ %σ₁ %ns %obs %obs' %nt Hσ with ⟨%Hred, H⟩
  imodintro
  isplitr
  · ipureintro; exact Hred
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  dsimp only [Nat.repeat]
  imod H $$ %e₂ %σ₂ %eₜ %Hstep Hcred with H
  iintro !> !>; imod H; iintro !>
  iapply step_fupdN_wand $$ H
  iintro H
  imod H with ⟨Hσ, H, Hefs⟩
  imod wp_ncfupd_post_step σ₂ (ns + 1) obs' (nt + eₜ.length) e₂ Φ $$ IH Hσ H with ⟨Hσ, H⟩
  imodintro
  iframe Hσ Hefs
  iexact H

end nc

end Perennial
