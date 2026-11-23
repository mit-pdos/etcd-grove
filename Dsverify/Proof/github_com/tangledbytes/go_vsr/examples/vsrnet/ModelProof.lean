/-
`Model()` (kit.go) meets the key-value map's porcupine model spec `kvS` (notes/dsv-vr.md, step 3):
the state's helpers `lookup`, `set`, `has`, `erase`, `push`, `equalPairs` and `step` over read-only
slices of `Pair`s, and the pure `stepG_pSeq`, `rep_eq` (`ModelSet.lean`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.ModelSet
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.ModelProofDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace github_com.tangledbytes.go_vsr.examples.vsrnet

open EtcdGrove EtcdGrove.linkv

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.tangledbytes.go_vsr.examples.vsrnet.Assumptions]
variable [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet

set_option goose.wp.extras true

theorem Model.wp_proof : Model.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_func_lits
  wp_auto
  iapply HΦ
  unfold isModel isEqHash
  simp only
  isplitr
  · ipureintro; trivial
  isplitr
  · -- Init
    unfold initSpec
    iintro !> %Φ' _ HΦ'
    wp_auto
    iapply HΦ'
    simp only [kvS, kvS0, kvRep]
    iexists slice.nil, slice.nil, [], []
    isplitr
    · ipureintro
      refine ⟨rfl, rep_init, ?_, ?_, ?_⟩
      · intro _ h; cases h
      · simp
      · simp
    simp only [pairsOf, List.map_nil]
    isplitr
    · iapply ownSlice_nil
    · iapply ownSlice_nil
  isplitr
  · -- Step
    iright
    isplitr
    · ipureintro; exact ⟨trivial, nofun⟩
    unfold stepSpec
    iintro %k %v %s %i %o
    iintro !> %Φ' Hpre HΦ'
    simp only [kvS, kvS0]
    icases Hpre with ⟨%Hk, Hrep, %Hio⟩
    obtain ⟨⟨x, rfl⟩, a, rfl⟩ := Hio
    unfold kvRep
    icases Hrep with ⟨%cur, %pend, %Cur, %Pend, %Hr, #Hc, #Hp⟩
    obtain ⟨rfl, hR, hP, hl1, hl2⟩ := Hr
    rw [inV_eq x, ansV_eq]
    wp_auto
    wp_apply wp_stepGo cur pend Cur Pend (by omega) (by omega) hP x a $$ [$Hc $Hp]
      as %ok %s' ⟨%cur', %pend', %Hst, #Hc', #Hp'⟩
    obtain ⟨rfl, rfl⟩ := Hst
    have H := stepG_pSeq hR x a
    have hpm := linkv.pM_step kvB kvDec s _ x a (kvDec_box x a)
    obtain ⟨hb1, hb2⟩ := stepG_bounds Cur Pend x a
    rw [← inV_eq x, ← ansV_eq]
    iapply HΦ'
    isplitr
    · iexists cur, pend, Cur, Pend
      iframe Hc Hp
      ipureintro; exact ⟨rfl, hR, hP, hl1, hl2⟩
    isplitr
    · ipureintro
      rw [hpm, H.1]
    · unfold stepPost
      simp only [hpm]
      cases hs : (pSeq kvB).step s (x, a) with
      | none => itrivial
      | some s' =>
        simp only
        iexists cur', pend', (stepG Cur Pend x a).2.1, (stepG Cur Pend x a).2.2
        iframe Hc' Hp'
        ipureintro
        exact ⟨rfl, H.2 s' hs, allPut_stepG hP Cur x a, by omega, by omega⟩
  isplitr
  · ipureintro; nofun
  isplitr
  · -- Equal
    unfold equalSpec
    iintro %k %j %v %w %s %t
    iintro !> %Φ' Hpre HΦ'
    simp only [kvS]
    unfold kvRep
    icases Hpre with ⟨⟨%cur, %pend, %Cur, %Pend, %Hr, #Hc, #Hp⟩,
      ⟨%cur', %pend', %Cur', %Pend', %Hr', #Hc', #Hp'⟩⟩
    obtain ⟨rfl, hR, hP, hl1, hl2⟩ := Hr
    obtain ⟨rfl, hR', hP', hl1', hl2'⟩ := Hr'
    ihave %HpL := ownSlice_len _ _ _ $$ Hp
    ihave %HpL' := ownSlice_len _ _ _ $$ Hp'
    wp_auto
    have back : ∀ b : Bool, (b = true → s = t) →
        ⊢ cur ↦*□ pairsOf Cur -∗ pend ↦*□ Pend.map pairK -∗ cur' ↦*□ pairsOf Cur' -∗
          pend' ↦*□ Pend'.map pairK -∗
          ((∃ (c p : GoSlice) (C : List (GoString × GoString)) (P : List KIn),
            ⌜interface.mkOk State.ty #(State.mk cur pend) = interface.mkOk State.ty #(State.mk c p) ∧
              Rep s C P ∧ AllPut P ∧ C.length ≤ k ∧ P.length ≤ k⌝ ∗
            c ↦*□ pairsOf C ∗ p ↦*□ P.map pairK) ∗
          (∃ (c p : GoSlice) (C : List (GoString × GoString)) (P : List KIn),
            ⌜interface.mkOk State.ty #(State.mk cur' pend') = interface.mkOk State.ty #(State.mk c p) ∧
              Rep t C P ∧ AllPut P ∧ C.length ≤ j ∧ P.length ≤ j⌝ ∗
            c ↦*□ pairsOf C ∗ p ↦*□ P.map pairK) ∗ ⌜b = true → s = t⌝ : IProp GF) := by
      intro b hb
      iintro #Hc #Hp #Hc' #Hp'
      isplitl
      · iexists cur, pend, Cur, Pend
        iframe Hc Hp
        ipureintro; exact ⟨rfl, hR, hP, hl1, hl2⟩
      isplitl
      · iexists cur', pend', Cur', Pend'
        iframe Hc' Hp'
        ipureintro; exact ⟨rfl, hR', hP', hl1', hl2'⟩
      ipureintro; exact hb
    by_cases h1 : pend.len = W64 0
    · rw [decide_eq_true h1]
      wp_auto
      by_cases h2 : pend'.len = W64 0
      · rw [decide_eq_true h2]
        wp_auto
        wp_apply wp_equalPairs cur cur' (pairsOf Cur) (pairsOf Cur') $$ [$Hc $Hc'] as %r %Hr
        iapply HΦ'
        iapply (back r ?_) $$ Hc Hp Hc' Hp'
        intro hr
        have e1 : Pend = [] := by
          have := HpL.1; rw [h1] at this; simp only [List.length_map] at this; exact List.eq_nil_of_length_eq_zero (this.trans rfl)
        have e2 : Pend' = [] := by
          have := HpL'.1; rw [h2] at this; simp only [List.length_map] at this; exact List.eq_nil_of_length_eq_zero (this.trans rfl)
        subst e1 e2
        rw [pairsOf_inj (Hr hr)] at hR
        exact rep_eq hR hR'
      · rw [decide_eq_false h2]
        wp_auto
        iapply HΦ'
        iapply (back false nofun) $$ Hc Hp Hc' Hp'
    · rw [decide_eq_false h1]
      wp_auto
      iapply HΦ'
      iapply (back false nofun) $$ Hc Hp Hc' Hp'
  ileft
  ipureintro; trivial

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
