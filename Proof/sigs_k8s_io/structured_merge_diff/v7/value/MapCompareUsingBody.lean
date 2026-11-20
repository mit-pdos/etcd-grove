/-
`value.MapCompareUsing`: a member of the recursion cluster `value.CompareUsingRec` (`CompareUsingRec.lean`); its proof is the
projection of the cluster's (its body is `MapCompareUsingBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.MapCompareUsingBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__Length
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.MapZipUsing
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsCompare
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsCmp
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsRec

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : value.Assumptions]

set_option hygiene false in
/-- `MapCompareUsing` after the lengths (`llength ↦ nl`, `rlength ↦ nr`), not both zero: the
lexical zip (internal to this proof). -/
local macro "map_cmp_main" : tactic => `(tactic| (
    ipersist llength
    ipersist rlength
    ipersist a
    wp_func_lits
    wp_apply h_MapZipUsing al _ _ ol or_ (W64 1) _
      (fun done => iprop(∃ (p xs ys : List (GoString × UVal)), c_ptr ↦ W64 0 ∗ i_ptr ↦ W64 p.length ∗
        ⌜kvsOrEmpty ol = p ++ xs ∧ kvsOrEmpty or_ = p ++ ys ∧ done = p.map (·.1)⌝))
      (iprop(∃ cv : w64, c_ptr ↦ cv ∗ ⌜cv ≠ W64 0 ∧ cv.toInt =
        ValueCompare.listCmp (ValueCompare.pairCmp UVal.compare) (kvsOrEmpty ol) (kvsOrEmpty or_)⌝))
      $$ [Ha c i] as %b ⟨Ha, Hpost⟩
    · iframe
      isplitr; iexact Hl
      isplitr; iexact Hr
      isplitr; ipureintro; right; rfl
      isplitr; ipureintro; intro _; omega
      isplitr
      · iunfold zipFnOk
        imodintro
        iintro %done %k %vl %vr %Hst %Φ' !> ⟨Ha, ⟨%p, %xs, %ys, Hc, Hi, %Hpd⟩, Hvl, Hvr⟩ HΦ'
        obtain ⟨hL, hR, rfl⟩ := Hpd
        obtain ⟨rest, hk⟩ := ValueCmp.mapCmp_next ol or_ p xs ys k hL hR (by simpa using Hst)
        have st := ValueCmp.mapCmp_step p xs ys k rest (hL ▸ hsl) (hR ▸ hsr) hk
        rw [← hL, ← hR] at st
        have hlp : p.length + xs.length = (kvsOrEmpty ol).length := by rw [hL]; simp
        have hrp : p.length + ys.length = (kvsOrEmpty or_).length := by rw [hR]; simp
        wp_auto
        by_cases hx : xs = []
        · have e : W64 (p.length : Int) = nl :=
            (ValueCmp.W64_len_iff Hnl hlenL (by omega)).2 (by subst hx; simp at hlp; omega)
          simp only [e, _root_.decide_true]
          wp_auto
          iapply HΦ'; simp only [Bool.false_eq_true, ↓reduceIte]; iframe
          ipureintro
          exact ⟨by decide, by rw [st.1 hx]; rfl⟩
        have e : W64 (p.length : Int) ≠ nl := fun h =>
          hx (List.eq_nil_of_length_eq_zero (by have := (ValueCmp.W64_len_iff Hnl hlenL (by omega)).1 h; omega))
        simp only [e, _root_.decide_false]
        wp_auto
        by_cases hy : ys = []
        · have e : W64 (p.length : Int) = nr :=
            (ValueCmp.W64_len_iff Hnr hlenR (by omega)).2 (by subst hy; simp at hrp; omega)
          simp only [e, _root_.decide_true]
          wp_auto
          iapply HΦ'; simp only [Bool.false_eq_true, ↓reduceIte]; iframe
          ipureintro
          exact ⟨by decide, by rw [st.2.1 hx hy]; rfl⟩
        have e : W64 (p.length : Int) ≠ nr := fun h =>
          hy (List.eq_nil_of_length_eq_zero (by have := (ValueCmp.W64_len_iff Hnr hlenR (by omega)).1 h; omega))
        simp only [e, _root_.decide_false]
        wp_auto
        cases hlk : lookupKV k (kvsOrEmpty ol) with
        | none =>
          iunfold optValF at Hvl; icases Hvl with %rfl
          wp_auto
          iapply HΦ'; simp only [Bool.false_eq_true, ↓reduceIte, optValF]; iframe
          ipureintro
          exact ⟨by decide, by rw [st.2.2.1 hx hy hlk]; rfl⟩
        | some x =>
          simp only [optValF]
          ihave %Hcl := isValF_concrete_law_holds vl _ x $$ Hvl
          obtain ⟨ql, rfl⟩ := Hcl
          wp_auto
          cases hrk : lookupKV k (kvsOrEmpty or_) with
          | none =>
            icases Hvr with %rfl
            wp_auto
            iapply HΦ'; simp only [Bool.false_eq_true, ↓reduceIte]; iframe
            ipureintro
            exact ⟨by decide, by rw [st.2.2.2.1 hx hy (by simp [hlk]) hrk]; rfl⟩
          | some y =>
            simp only [optValF]
            ihave %Hcr := isValF_concrete_law_holds vr _ y $$ Hvr
            obtain ⟨qr, rfl⟩ := Hcr
            wp_auto
            have hokx : UVal.mapLensOk x = true :=
              ValueCmp.mapLensOkM_mem (ValuePure.lookupKV_mem' hlk) hokL
            have hoky : UVal.mapLensOk y = true :=
              ValueCmp.mapLensOkM_mem (ValuePure.lookupKV_mem' hrk) hokR
            wp_apply HC $$ %al %_ %_ %(DFrac.own 1) %(DFrac.own 1) %x %y [Ha Hvl Hvr]
              as %cr ⟨Ha, Hvl, Hvr, %Hcr⟩
            · iframe; ipureintro; exact ⟨hokx, hoky⟩
            obtain ⟨hxs, hys, hc⟩ := st.2.2.2.2 x y hlk hrk
            have hplt : p.length < 2 ^ 61 := by
              have : xs.length ≠ 0 := fun h => hx (List.eq_nil_of_length_eq_zero h)
              omega
            try wp_auto
            by_cases hc0 : cr = W64 0
            · subst hc0
              have hxy : UVal.compare x y = 0 := by rw [← Hcr]; rfl
              have exy := ValueCompare.compare_eq x y hxy
              subst exy
              rw [show decide ((W64 0 : w64) = W64 0) = true by simp]
              iapply HΦ'; simp only [↓reduceIte]; iframe
              iexists p ++ [(k, x)], xs.tail, ys.tail
              rw [ValueCmp.W64_succ _ hplt]
              simp only [List.length_append, List.length_singleton]
              iframe; ipureintro
              refine ⟨?_, ?_, by simp⟩
              · rw [hL, hxs]; simp
              · rw [hR, hys]; simp
            · rw [decide_eq_false hc0]
              iapply HΦ'; simp only [Bool.false_eq_true, ↓reduceIte]; iframe
              ipureintro
              have hne : UVal.compare x y ≠ 0 := fun h =>
                hc0 (BitVec.eq_of_toInt_eq (by rw [Hcr, h]; rfl))
              refine ⟨hc0, ?_⟩
              rw [hc]; simp only [hne, ↓reduceIte]; exact Hcr
      iexists [], kvsOrEmpty ol, kvsOrEmpty or_
      isplitl [i]
      · simp only [List.length_nil, Int.natCast_zero]; iexact i
      · ipureintro; simp
    iunfold mapIterPost at Hpost
    cases b
    · isimp at Hpost
      icases Hpost with ⟨%cv, Hc, %Hcv⟩
      wp_auto
      iapply HΦ; iframe; ipureintro
      rw [ValueCompare.compare_map]; exact Hcv.2
    · isimp at Hpost
      icases Hpost with ⟨%done, %Hd, %p, %xs, %ys, Hc, Hi, %Hp⟩
      obtain ⟨hL, hR, rfl⟩ := Hp
      have heq := ValueCmp.mapCmp_done ol or_ p xs ys hL hR (by simpa using Hd)
      wp_auto
      iapply HΦ; iframe; ipureintro
      rw [heq, ValueCompare.compare_self]; rfl))

set_option hygiene false in
/-- `MapCompareUsing` on two empty maps: `0`. -/
local macro "map_cmp_empty" : tactic => `(tactic| (
    iapply HΦ; iframe; ipureintro
    have h1 : (kvsOrEmpty ol).length = 0 := by
      have := Hnl; rw [hz1] at this; simp at this; omega
    have h2 : (kvsOrEmpty or_).length = 0 := by
      have := Hnr; rw [hz2] at this; simp at this; omega
    rw [List.eq_nil_of_length_eq_zero h1, List.eq_nil_of_length_eq_zero h2]; rfl))

set_option hygiene false in
/-- `MapCompareUsing` after the lengths: the early return on two empty maps, else the zip. -/
local macro "map_cmp_tail" : tactic => `(tactic| (
    by_cases hz1 : nl = W64 0
    · rw [decide_eq_true hz1]
      wp_auto
      by_cases hz2 : nr = W64 0
      · rw [decide_eq_true hz2]
        wp_auto
        map_cmp_empty
      · rw [decide_eq_false hz2]
        wp_auto
        map_cmp_main
    · rw [decide_eq_false hz1]
      wp_auto
      map_cmp_main))

theorem value.MapCompareUsing.wp_proofBody
    (h_mapUnstructuredString_Length : value.mapUnstructuredString.Length.spec (GF := GF))
    (h_MapZipUsing : value.MapZipUsing.spec (GF := GF)) :
    value.MapCompareUsing.specBody (GF := GF) := by
  iintro #IH
  iunfold value.MapCompareUsing.specI
  iintro %al %lm %rm %ol %or_
  wp_start as ⟨Ha, #Hl, #Hr, %Hok⟩
  iunfold value.CompareUsingRec.specI at IH
  icases IH with ⟨#HC, -, -⟩
  iunfold value.CompareUsing.specI at HC
  ihave %hsl : ⌜keysSorted (kvsOrEmpty ol) = true⌝ $$ [Hl]
  · cases ol with
    | none => ipureintro; rfl
    | some l => simp only [isMapO, kvsOrEmpty, Option.getD_some]; iapply (isMapV_sorted_law_holds _ _); iexact Hl
  ihave %hsr : ⌜keysSorted (kvsOrEmpty or_) = true⌝ $$ [Hr]
  · cases or_ with
    | none => ipureintro; rfl
    | some r => simp only [isMapO, kvsOrEmpty, Option.getD_some]; iapply (isMapV_sorted_law_holds _ _); iexact Hr
  obtain ⟨hlenL, hokL⟩ := ValueCmp.mapLensOk_map Hok.1
  obtain ⟨hlenR, hokR⟩ := ValueCmp.mapLensOk_map Hok.2
  ihave %Hlc := isMapO_cases lm ol $$ Hl
  ihave %Hrc := isMapO_cases rm or_ $$ Hr
  rcases Hlc with ⟨hol, rfl⟩ | ⟨l, gl, hol, rfl⟩ <;> rcases Hrc with ⟨hor, rfl⟩ | ⟨r, gr, hor, rfl⟩
  · wp_auto
    iapply HΦ; iframe; ipureintro; subst hol hor; rfl
  · wp_auto
    wp_apply h_mapUnstructuredString_Length gr r as %nr %Hnr
    · subst hor; iunfold isMapO at Hr; iexact Hr
    try wp_auto
    generalize hnl0 : (zero_val w64 : w64) = nl
    have Hnl : nl.toInt = (kvsOrEmpty ol).length := by subst hol hnl0; rfl
    replace Hnr : nr.toInt = (kvsOrEmpty or_).length := by simp [hor, kvsOrEmpty, Hnr]
    have hz1 : nl = W64 0 := hnl0.symm
    by_cases hz2 : nr = W64 0
    · rw [decide_eq_true hz2]
      wp_auto
      map_cmp_empty
    · rw [decide_eq_false hz2]
      wp_auto
      map_cmp_main
  · wp_auto
    wp_apply h_mapUnstructuredString_Length gl l as %nl %Hnl
    · subst hol; iunfold isMapO at Hl; iexact Hl
    try wp_auto
    generalize hnr0 : (zero_val w64 : w64) = nr
    have Hnr : nr.toInt = (kvsOrEmpty or_).length := by subst hor hnr0; rfl
    replace Hnl : nl.toInt = (kvsOrEmpty ol).length := by simp [hol, kvsOrEmpty, Hnl]
    map_cmp_tail
  · wp_auto
    wp_apply h_mapUnstructuredString_Length gl l as %nl %Hnl
    · subst hol; iunfold isMapO at Hl; iexact Hl
    try wp_auto
    wp_apply h_mapUnstructuredString_Length gr r as %nr %Hnr
    · subst hor; iunfold isMapO at Hr; iexact Hr
    try wp_auto
    replace Hnl : nl.toInt = (kvsOrEmpty ol).length := by simp [hol, kvsOrEmpty, Hnl]
    replace Hnr : nr.toInt = (kvsOrEmpty or_).length := by simp [hor, kvsOrEmpty, Hnr]
    map_cmp_tail


end proof

end smd
end EtcdGrove
end Perennial
