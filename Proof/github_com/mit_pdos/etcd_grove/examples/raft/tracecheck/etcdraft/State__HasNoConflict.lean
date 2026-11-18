/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__HasNoConflict`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__HasNoConflict

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

theorem State.HasNoConflict.wp_proof : State.HasNoConflict.spec (GF := GF) (hG := hG) := by
  intro p st i index el ents
  wp_start as ⟨#Hst, #Hents, %Hi, %hx1, %hx2, %hll, %hel⟩
  read_server
  iunfold logRO at Hents
  icases Hents with ⟨%fs, #Hfs, #Hfl⟩
  ihave %Hfsl := ownSlice_len $$ Hfs
  ihave %Hfll := BigSepL2.bigSepL2_length $$ Hfl
  wp_auto
  lookup_server
  have hlen : sint.Z gs.Log'.len = ((st.s (uint.nat i)).log.length : Int) := by rw [← Hell, Hesl.1]; word
  have hflen : sint.Z el.len = (ents.length : Int) := by rw [← Hfll, Hfsl.1]; word
  have hl1 : sint.Z (gs.Log'.len + W64 1) = ((st.s (uint.nat i)).log.length : Int) + 1 := by rw [← hlen]; word
  rw [hl1]
  by_cases h0 : ((st.s (uint.nat i)).log.length : Int) + 1 < sint.Z index
  · rw [decide_eq_true h0]
    wp_auto
    have : st.hasNoConflict (uint.nat i) (sint.Z index) ents = false := by
      unfold State.hasNoConflict
      have : ¬ (sint.Z index ≤ ((st.s (uint.nat i)).log.length : Int) + 1) := by omega
      simp [this]
    rw [this]; iapply HΦ; ipureintro; trivial
  rw [decide_eq_false h0]
  wp_auto
  obtain ⟨P, hP⟩ : ∃ P : Nat → Bool, P = (fun (k : Nat) => Bool.or (Bool.not (decide (sint.Z index + (k : Int) ≤ ((st.s (uint.nat i)).log.length : Int)))) ((((st.s (uint.nat i)).log[(sint.Z index + (k : Int) - 1).toNat]?).map Entry.term) == ((ents[k]?).map Entry.term))) := ⟨_, rfl⟩
  have hnc : st.hasNoConflict (uint.nat i) (sint.Z index) ents = Bool.and (decide (sint.Z index ≤ ((st.s (uint.nat i)).log.length : Int) + 1)) ((List.range ents.length).all P) := by
    rw [hP]; rfl
  ihave IH : iprop(∃ (k : w64),
      "k" ∷ k_ptr ↦ k ∗
      "%Hk" ∷ ⌜1 ≤ sint.Z k ∧ sint.Z k ≤ (ents.length : Int) + 1 ∧
        (List.range (sint.nat k - 1)).all P = true⌝) $$ [k]
  · iexists _
    iframe
    ipureintro
    rw [show sint.Z (W64 1) = 1 from rfl, show sint.nat (W64 1) = 1 from rfl]
    refine ⟨Int.le_refl _, by omega, by simp⟩
  wp_for IH
  obtain ⟨hk1, hk2, hka⟩ := Hk
  have hkk : ((sint.nat k : Nat) : Int) = sint.Z k := by word
  by_cases hc : sint.Z k ≤ (ents.length : Int)
  rotate_left
  · have hd : decide (sint.Z k ≤ sint.Z el.len) = false := by rw [hflen]; simpa using hc
    simp only [hd, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    have hall : (List.range ents.length).all P = true := by
      have : sint.nat k - 1 = ents.length := by omega
      rw [← this]; exact hka
    rw [hnc, hall]
    simp only [Bool.and_true]
    rw [decide_eq_true (by omega)]
    iapply HΦ; ipureintro; trivial
  have hd : decide (sint.Z k ≤ sint.Z el.len) = true := by rw [hflen]; simpa using hc
  simp only [hd, ↓reduceIte]
  wp_auto
  have hs1 : sint.Z (index + k - W64 1) = sint.Z index + sint.Z k - 1 := by word
  have hstep : (List.range (sint.nat (k + W64 1) - 1)).all P =
      ((List.range (sint.nat k - 1)).all P && P (sint.nat k - 1)) := by
    rw [show sint.nat (k + W64 1) - 1 = sint.nat k - 1 + 1 by word, List.range_succ]
    simp
  rw [hs1, hlen]
  by_cases c1 : sint.Z index + sint.Z k - 1 ≤ ((st.s (uint.nat i)).log.length : Int)
  rotate_left
  · rw [decide_eq_false c1]
    wp_auto
    wp_for_post
    iframe
    iexists _
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    rw [hstep, hka]
    have : P (sint.nat k - 1) = true := by
      rw [hP]; simp only [Bool.or_eq_true, Bool.not_eq_true']
      left; simp; omega
    simp [this]
  rw [decide_eq_true c1]
  wp_auto
  have hs2 : sint.Z (index + k - W64 2) = sint.Z index + sint.Z k - 2 := by word
  have hs3 : sint.Z (k - W64 1) = sint.Z k - 1 := by word
  have hi2 : 0 ≤ sint.Z (index + k - W64 2) ∧ sint.Z (index + k - W64 2) < sint.Z gs.Log'.len := by
    rw [hs2, hlen]; omega
  have hi3 : 0 ≤ sint.Z (k - W64 1) ∧ sint.Z (k - W64 1) < sint.Z el.len := by
    rw [hs3, hflen]; omega
  rw [ite_eq_left_of_eq_true _ _ (eq_true hi2)]
  have hn2 : (sint.Z (index + k - W64 2)).toNat < es.length := by rw [Hell, hs2]; omega
  obtain ⟨x, Hx⟩ : ∃ x, es[(sint.Z (index + k - W64 2)).toNat]? = some x := ⟨_, List.getElem?_eq_getElem hn2⟩
  obtain ⟨y, Hy⟩ : ∃ y, (st.s (uint.nat i)).log[(sint.Z (index + k - W64 2)).toNat]? = some y :=
    ⟨_, List.getElem?_eq_getElem (Hell ▸ hn2)⟩
  ihave #Hxy := BigSepL2.bigSepL2_lookup (Φ := fun _ e x => entryRO (GF := GF) e x) Hx Hy $$ Hel
  iunfold entryRO at Hxy
  icases Hxy with ⟨%Hxy1, -⟩
  icases ownSlice_elem_acc _ x _ _ es hi2.1 Hx $$ Hes with ⟨#Hxe, -⟩
  icases typedPointsto_split _ _ _ $$ Hxe with Hxef
  simp only [TypedPointsto.typedPointstoDef]
  icases Hxef with ⟨#E1, #E2, #E3, -⟩
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true hi3)]
  have hn3 : (sint.Z (k - W64 1)).toNat < fs.length := by rw [Hfll, hs3]; omega
  obtain ⟨x2, Hx2⟩ : ∃ x, fs[(sint.Z (k - W64 1)).toNat]? = some x := ⟨_, List.getElem?_eq_getElem hn3⟩
  obtain ⟨y2, Hy2⟩ : ∃ y, ents[(sint.Z (k - W64 1)).toNat]? = some y :=
    ⟨_, List.getElem?_eq_getElem (Hfll ▸ hn3)⟩
  ihave #Hxy2 := BigSepL2.bigSepL2_lookup (Φ := fun _ e x => entryRO (GF := GF) e x) Hx2 Hy2 $$ Hfl
  iunfold entryRO at Hxy2
  icases Hxy2 with ⟨%Hxy3, -⟩
  icases ownSlice_elem_acc _ x2 _ _ fs hi3.1 Hx2 $$ Hfs with ⟨#Hxe2, -⟩
  icases typedPointsto_split _ _ _ $$ Hxe2 with Hxef2
  simp only [TypedPointsto.typedPointstoDef]
  icases Hxef2 with ⟨#F1, #F2, #F3, -⟩
  wp_auto
  have hPk : P (sint.nat k - 1) = decide (y.term = y2.term) := by
    rw [hP]
    have e1 : (sint.Z index + ((sint.nat k - 1 : Nat) : Int) - 1).toNat = (sint.Z (index + k - W64 2)).toNat := by
      rw [hs2]; omega
    have e2 : sint.nat k - 1 = (sint.Z (k - W64 1)).toNat := by rw [hs3]; omega
    have c1' : sint.Z index + ((sint.nat k - 1 : Nat) : Int) ≤ ((st.s (uint.nat i)).log.length : Int) := by omega
    simp only [c1', _root_.decide_true, Bool.not_true, Bool.false_or, e1, Hy]
    rw [e2, Hy2]; simp only [Option.map_some]
    by_cases h : y.term = y2.term <;> simp [h]
  have he := sint_eq_iff x.Term' x2.Term' _ _ Hxy1.1 Hxy3.1
  by_cases c2 : y.term = y2.term
  · rw [decide_eq_true (he.2 c2)]
    wp_auto
    wp_for_post
    iframe
    iexists _
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    rw [hstep, hka, hPk, decide_eq_true c2]
  · rw [decide_eq_false (fun e => c2 (he.1 e))]
    wp_auto
    wp_for_post
    try wp_auto
    have : st.hasNoConflict (uint.nat i) (sint.Z index) ents = false := by
      rw [hnc]
      have : (List.range ents.length).all P = false := by
        rw [List.all_eq_false]
        exact ⟨sint.nat k - 1, by simp; omega, by rw [hPk, decide_eq_false c2]; simp⟩
      rw [this]; simp
    rw [this]; iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
