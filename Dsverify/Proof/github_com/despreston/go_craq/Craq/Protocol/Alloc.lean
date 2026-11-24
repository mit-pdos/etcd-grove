/-
The protocol's start (`craq_alloc`).
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Protocol.Simple

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

namespace github_com.despreston.go_craq

section alloc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- A chain address's ghost state at the start. -/
def nodeInit (γ : CraqNames) (a : GoString) : IProp GF :=
  iprop(roleHalf γ a ((false, go!"") : Role) ∗ roleHalf γ a ((false, go!"") : Role) ∗
    nlogAuth γ a [] ∗ joinTicket γ a)

theorem nodeInit_congr (γ γ' : CraqNames) (a : GoString) (hr : γ.role a = γ'.role a)
    (hn : γ.nlog a = γ'.nlog a) (hj : γ.join a = γ'.join a) :
    nodeInit (GF := GF) γ a = nodeInit γ' a := by
  unfold nodeInit roleHalf nlogAuth joinTicket
  rw [hr, hn, hj]

/-- The names of a run from the global ones and the per-node functions. -/
def mkNames (γa γc γn γr : GName) (fr fn fj : GoString → GName) : CraqNames :=
  ⟨γa, γc, γn, γr, fr, fn, fj⟩

theorem alloc_nodes (γa γc γn γr : GName) (ads : List GoString) (hads : ads.Nodup) :
    ⊢ |==> ∃ fr fn fj : GoString → GName,
      [∗list] a ∈ ads, nodeInit (GF := GF) (mkNames γa γc γn γr fr fn fj) a := by
  induction ads with
  | nil =>
    imodintro
    iexists (fun _ => 0), (fun _ => 0), (fun _ => 0)
    iapply BigSepL.bigSepL_nil.2
    itrivial
  | cons a ads ih =>
    have hnot : a ∉ ads := (List.nodup_cons.1 hads).1
    imod ih (List.nodup_cons.1 hads).2 with ⟨%fr, %fn, %fj, Hs⟩
    imod ghostVar_alloc (GF := GF) ((false, go!"") : Role) with ⟨%γro, Hro⟩
    imod mono_list_own_alloc (GF := GF) ([] : CLog) with ⟨%γnl, Hnl, -⟩
    imod token_alloc (GF := GF) with ⟨%γj, Hj⟩
    icases (ghostVar_split_half γro 1 _).1 $$ Hro with ⟨Hro1, Hro2⟩
    imodintro
    iexists (fun b => if b = a then γro else fr b), (fun b => if b = a then γnl else fn b),
      (fun b => if b = a then γj else fj b)
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hro1 Hro2 Hnl Hj]
    · unfold nodeInit mkNames roleHalf nlogAuth joinTicket
      simp only [↓reduceIte]
      iframe
    iapply BigSepL.bigSepL_mono ?_ $$ Hs
    intro k b hb
    have hba : b ≠ a := fun h => hnot (h ▸ List.mem_of_getElem? hb)
    rw [nodeInit_congr (mkNames γa γc γn γr fr fn fj)
      (mkNames γa γc γn γr (fun b => if b = a then γro else fr b)
        (fun b => if b = a then γnl else fn b) (fun b => if b = a then γj else fj b)) b
      (by simp [mkNames, hba]) (by simp [mkNames, hba]) (by simp [mkNames, hba])]

theorem craq_alloc.holds : craq_alloc.spec (GF := GF) (G := G) := by
  intro ads hads
  imod ghostVar_alloc (GF := GF) ([] : List (GoString × GoString)) with ⟨%γa, Ha⟩
  imod mono_list_own_alloc (GF := GF) ([] : CLog) with ⟨%γc, Hc, -⟩
  imod ghostVar_alloc (GF := GF) (W64 0) with ⟨%γn, Hn⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := RecInfo) with ⟨%γr, Hr⟩
  imod alloc_nodes (GF := GF) γa γc γn γr ads hads with ⟨%fr, %fn, %fj, Hs⟩
  icases (ghostVar_split_half γa 1 _).1 $$ Ha with ⟨Ha1, Ha2⟩
  icases (cv_halves γc _).1 $$ Hc with ⟨Hc1, Hc2⟩
  icases (ghostVar_split_half γn 1 _).1 $$ Hn with ⟨Hn1, Hn2⟩
  imod inv_alloc craqN ⊤ (craqInv (mkNames γa γc γn γr fr fn fj)) $$ [Ha1 Hc1 Hn1 Hr] with #Hinv
  · inext
    unfold craqInv mkNames
    iexists ([] : List (GoString × GoString)), ([] : CLog), W64 0, (∅ : GMap w64 RecInfo)
    iframe
    isplitr
    · ipureintro
      refine ⟨fun v => ?_, fun k => ?_, fun k h => absurd rfl h, fun v ri h => ?_⟩
      · simp only [GMap.lookup_empty, Option.isSome_none, Bool.false_eq_true, false_iff]
        have : uint.Z (W64 0) = 0 := rfl
        omega
      · rfl
      · simp at h
    isplitr
    · iapply BigSepM.bigSepM_empty.2
      itrivial
    iapply BigSepM.bigSepM_empty.2
    itrivial
  imodintro
  iexists mkNames γa γc γn γr fr fn fj
  isplitr
  · unfold isCraq; iexact Hinv
  isplitl [Ha2]
  · unfold ownState mkNames
    iexists []
    iframe Ha2
    ipureintro; exact kvOfPuts_nil.symm
  isplitl [Hc2]
  · unfold tailTok mkNames; iexact Hc2
  isplitl [Hn2]
  · unfold nextHalf mkNames; iexact Hn2
  unfold nodeInit
  iexact Hs

end alloc

end github_com.despreston.go_craq

end Perennial
