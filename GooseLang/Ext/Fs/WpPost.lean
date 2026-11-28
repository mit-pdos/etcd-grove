/-
A weakest precondition of one operation of an extension, strengthened by what every step of the
semantics' operation returns (`wp_ext_post`): when each step of `o` on `v` (in the semantics the
program runs, which may be restricted by a premise, `Premises.lean`) ends in a value `r` with `Ψ r`,
a proof of `WP (ExternalOp X.name o v) {{ r, ⌜Ψ r⌝ -∗ Φ r }}` is one of `WP … {{ Φ }}`. It lets a
spec of the operation proved over any semantics (with its error arms) give, over a semantics whose
premise rules the errors out, a spec without them, from the spec itself. Untrusted.
-/
module

public import Perennial.GooseLang.Lifting

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open EctxLanguage

section post
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- Every step of an extension's operation (in the program's semantics) is a step of the
extension's semantics. -/
theorem extOp_step_inv {X : GooseExt} [ExtSemantics X] [ExtInterp X] [hX : HasExt X] (o : String) (v : val)
    (hv : v.isPanic = false) {σ₁ : BcfgState} {obs e₂ σ₂ eₜ}
    (hst : PrimStep.primStep (ExternalOp X.name o (Val v), σ₁) obs (e₂, σ₂, eₜ)) :
    ∃ tf h g h' σ' g',
      ExtSemantics.step (E := X) tf o v h (hX.mem.get σ₁.1.1.world) g e₂ h' σ' g' := by
  have hsub : SubredexesAreValues (ExternalOp X.name o (Val v)) :=
    EctxItemLanguage.subredexes_are_values (fun Ki e' h => by
      cases Ki <;> (try simp only [fillItem] at h) <;> cases h <;> rfl)
  have hb := baseStep_of_primStep hst hsub
  rcases σ₁ with ⟨σ, f⟩
  obtain ⟨σ', -, hh⟩ := (boundedBaseStep_plain (σ := σ) (f := f) rfl).1 hb
  have hnu : ∀ p, ¬ Unwinds (ExternalOp X.name o (Val v)) p := by not_unwinds
  cases baseStep_of_headStep hnu hh with
  | ExternalOpS _ _ _ _ _ _ Hst =>
    obtain ⟨h', σ'', g', Hst', -⟩ := (extStep_named _ _ _ _ _).1 Hst
    exact ⟨_, _, _, h', σ'', g', (HasExt.step_iff ..).1 Hst'⟩

/-- **A weakest precondition of an extension's operation, strengthened by its steps** (see the file
header). -/
theorem wp_ext_post {X : GooseExt} [ExtSemantics X] [ExtInterp X] [hX : HasExt X] (o : String) (v : val)
    (hv : v.isPanic = false) (Ψ : val → Prop)
    (hΨ : ∀ {tf : GoTypeFns} h σ g e' h' σ' g', ExtSemantics.step (E := X) tf o v h σ g e' h' σ' g' →
      ∃ r, e' = Val r ∧ Ψ r)
    (Φ : val → IProp GF) :
    WP (ExternalOp X.name o (Val v)) @ s; E {{ r, ⌜Ψ r⌝ -∗ Φ r }} ⊢
      WP (ExternalOp X.name o (Val v)) @ s; E {{ Φ }} := by
  have h' : ToVal.toVal (Val := val) (ExternalOp X.name o (Val v)) = none := rfl
  iintro Hwp
  iapply wp_unfold.2
  ihave Hwp := wp_unfold.1 $$ Hwp
  unfold wp.pre
  rw [h']
  dsimp only
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  imod Hwp $$ %σ₁ %ns %obs %obs' %nt Hσ with ⟨%Hred, H⟩
  imodintro
  isplitr
  · ipureintro; exact Hred
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  obtain ⟨tf, h, g, h', σ', g', Hst⟩ := extOp_step_inv o v hv Hstep
  obtain ⟨r, rfl, hr⟩ := hΨ _ _ _ _ _ _ _ Hst
  ihave H := H $$ %(Val r) %σ₂ %eₜ %Hstep Hcred
  iapply step_fupdN_wand $$ H
  iintro H
  imod H with ⟨Hσ, Hwp, Hefs⟩
  imodintro
  iframe Hσ Hefs
  iapply wp_value_fupd'.2
  imod wp_value_fupd'.1 $$ Hwp with Hwp
  imodintro
  iapply Hwp
  ipureintro; exact hr

/-- **`wp_ext_post` with a fact of the state** from a resource `P` the caller holds at the call
(`hP`: `P` and the extension's interpretation of its state `σ` give `R σ`); the step from such a
state ends in a value with `Ψ`. `P` goes to the proof of the operation's spec, after the fact is
read off the state the step starts from (the operation being one step, the state is the step's). -/
theorem wp_ext_postS {X : GooseExt} [ExtSemantics X] [I : ExtInterp X] [hX : HasExt X]
    (o : String) (v : val) (hv : v.isPanic = false) (P : IProp GF) (R : X.LocalState → Prop)
    (hP : ∀ σ, iprop(P ∗ I.localCtx (extLocalGS X) σ) ⊢ ⌜R σ⌝) (Ψ : val → Prop)
    (hΨ : ∀ {tf : GoTypeFns} h σ g e' h' σ' g', R σ →
      ExtSemantics.step (E := X) tf o v h σ g e' h' σ' g' →
      ∃ r, e' = Val r ∧ Ψ r)
    (Φ : val → IProp GF) :
    ⊢ P -∗ (P -∗ WP (ExternalOp X.name o (Val v)) @ s; E {{ r, ⌜Ψ r⌝ -∗ Φ r }}) -∗
      WP (ExternalOp X.name o (Val v)) @ s; E {{ Φ }} := by
  have h' : ToVal.toVal (Val := val) (ExternalOp X.name o (Val v)) = none := rfl
  iintro HP Hwp
  iapply wp_unfold.2
  unfold wp.pre
  rw [h']
  dsimp only
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  rcases σ₁ with ⟨σ, c⟩
  icases (goose_bstateInterp_eq σ c ns (obs ++ obs') nt).1 $$ Hσ with ⟨Hσ, Hc, Ht, Hnc⟩
  icases (goose_stateInterp_eq σ ns (obs ++ obs') nt).1 $$ Hσ with
    ⟨Hheap, Hext, Hgs, %Hlctx, Hgext, Hproph⟩
  icases HasExt.localCtx_acc (X := X) _ $$ Hext with ⟨Hl, Hlclose⟩
  icases persistent_entails_right (hP (hX.mem.get σ.1.world)) $$ [HP Hl] with ⟨%hR, HP, Hl⟩
  · iframe
  ihave Hσ : stateInterp (GF := GF) ((σ, c) : BcfgState) ns (obs ++ obs') nt $$
    [Hheap Hl Hlclose Hgs Hgext Hproph Hc Ht Hnc]
  · iapply (goose_bstateInterp_eq σ c ns (obs ++ obs') nt).2
    iframe Hc Ht Hnc
    iapply (goose_stateInterp_eq σ ns (obs ++ obs') nt).2
    ihave Hl := Hlclose $$ Hl
    rw [ExtIn.set_get]
    iframe
    ipureintro; exact Hlctx
  ihave Hwp := Hwp $$ HP
  ihave Hwp := wp_unfold.1 $$ Hwp
  unfold wp.pre
  rw [h']
  dsimp only
  imod Hwp $$ %(σ, c) %ns %obs %obs' %nt Hσ with ⟨%Hred, H⟩
  imodintro
  isplitr
  · ipureintro; exact Hred
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  obtain ⟨tf, h, g, h', σ', g', Hst⟩ := extOp_step_inv o v hv Hstep
  obtain ⟨r, rfl, hr⟩ := hΨ _ _ _ _ _ _ _ hR Hst
  ihave H := H $$ %(Val r) %σ₂ %eₜ %Hstep Hcred
  iapply step_fupdN_wand $$ H
  iintro H
  imod H with ⟨Hσ, Hwp, Hefs⟩
  imodintro
  iframe Hσ Hefs
  iapply wp_value_fupd'.2
  imod wp_value_fupd'.1 $$ Hwp with Hwp
  imodintro
  iapply Hwp
  ipureintro; exact hr

end post

end Perennial

end
