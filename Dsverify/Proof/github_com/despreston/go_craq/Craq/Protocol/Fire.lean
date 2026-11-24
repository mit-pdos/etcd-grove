/-
Firing a deposited put's atomic update (the core step of `commit`), and the masks.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Protocol.Simple

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

namespace github_com.despreston.go_craq

theorem craqN_clientMask_disj : (↑craqN : CoPset) ## clientMask := by
  intro p ⟨h1, h2⟩
  unfold clientMask craqEop at h2
  exact (LawfulSet.mem_diff.1 h2).2 (LawfulSet.mem_union.2 (Or.inl h1))

theorem clientN_sub_diff {E : CoPset} (hE : ↑craqN ∪ clientMask ⊆ E) :
    clientMask ⊆ E \ ↑craqN := by
  intro p hp
  refine LawfulSet.mem_diff.2 ⟨hE p (LawfulSet.mem_union.2 (Or.inr hp)), fun h => ?_⟩
  exact craqN_clientMask_disj p ⟨h, hp⟩

theorem craqN_sub {E : CoPset} (hE : ↑craqN ∪ clientMask ⊆ E) : (↑craqN : CoPset) ⊆ E :=
  fun p hp => hE p (LawfulSet.mem_union.2 (Or.inl hp))

section fire
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **A client's update fires** (from any mask holding `clientMask`) against the invariant's
half of the abstract state: the new state, and the caller's postcondition of the step's output. -/
theorem opAU_commit (γ : CraqNames) (E : CoPset) (hE : clientMask ⊆ E) (i : KvM.Input)
    (Q : KvM.Output → IProp GF) (l : List (GoString × GoString)) :
    ⊢ ghostVar (GF := GF) γ.abs (1 : Qp).half l -∗ opAU γ i Q ={E}=∗
      ∃ l', ghostVar γ.abs (1 : Qp).half l' ∗ ⌜kvOfPuts l' = (KvM.stepF i (kvOfPuts l)).1⌝ ∗
        ⌜(∀ k x, i = .put k x → l' = (k, x) :: l) ∧ (∀ k, i = .get k → l' = l)⌝ ∗
        Q (KvM.stepF i (kvOfPuts l)).2 := by
  iintro Habs HAU
  unfold opAU
  imod fupd_mask_subseteq (PROP := IProp GF) hE with Hmask
  imod HAU with ⟨%σ, Hown, Hcommit⟩
  unfold ownState
  icases Hown with ⟨%l, %Hσ, Hown⟩
  ihave %Hag := ghostVar_agree _ _ _ _ _ $$ Habs Hown
  subst Hag Hσ
  cases i with
  | put k x =>
    imod ghostVar_update_halves ((k, x) :: l) $$ Habs Hown with ⟨Habs, Hown⟩
    imod Hcommit $$ [Hown] with HQ
    · iexists ((k, x) :: l)
      iframe Hown
      ipureintro
      rw [kvOfPuts_put_stepF]
    imod Hmask
    imodintro
    iexists ((k, x) :: l)
    iframe Habs HQ
    isplitr
    · ipureintro; rw [kvOfPuts_put_stepF]
    ipureintro
    exact ⟨fun k' x' h => by cases h; rfl, fun _ h => KvInput.noConfusion h⟩
  | get k =>
    imod Hcommit $$ [Hown] with HQ
    · iexists l
      iframe Hown
      ipureintro; rfl
    imod Hmask
    imodintro
    iexists l
    iframe Habs HQ
    isplitr
    · ipureintro; rfl
    ipureintro
    exact ⟨fun _ _ h => KvInput.noConfusion h, fun _ _ => rfl⟩

/-- Fire a pending put's update against the invariant's half of the abstract state. -/
theorem fire_put (γ : CraqNames) (E : CoPset) (hE : clientMask ⊆ E)
    (l : List (GoString × GoString)) (ri : RecInfo) :
    ⊢ ghostVar (GF := GF) γ.abs (1 : Qp).half l -∗ recRes γ ri false ={E}=∗
      ghostVar γ.abs (1 : Qp).half ((ri.key, ri.val) :: l) ∗ recRes γ ri true := by
  iintro Habs Hr
  unfold recRes
  simp only [Bool.false_eq_true, ↓reduceIte]
  icases Hr with ⟨%Q, #Hsp, HAU⟩
  imod opAU_commit γ E hE (.put ri.key ri.val) Q l $$ Habs HAU with ⟨%l', Habs, -, %Hput, HQ⟩
  rw [Hput.1 ri.key ri.val rfl]
  imodintro
  iframe Habs
  iexists (putReceipt ri.key ri.val Q)
  iframe Hsp
  ileft
  unfold putReceipt
  iapply (show Q (KvM.stepF (.put ri.key ri.val) (kvOfPuts l)).2 ⊢ Q .done from .rfl) $$ HQ

end fire

end github_com.despreston.go_craq

end Perennial
