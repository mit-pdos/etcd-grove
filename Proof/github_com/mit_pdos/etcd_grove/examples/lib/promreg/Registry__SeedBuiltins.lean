/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/lib/promreg/Registry__SeedBuiltins.lean`. Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.promreg.Registry__SeedBuiltins
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode
open _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.lib

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [promG : promreg.PromRegGS GF]
variable [package_sem : promreg.Assumptions]

theorem promreg.wp_BuiltinIDs :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.promreg }}
      (App (Val (@! promreg.BuiltinIDs)) (Val #()))
    {{ (s : GoSlice), RET #s; s ↦* promreg.builtinIDs }} := by
  wp_start
  wp_auto
  wp_apply wp_slice_literal (l := promreg.builtinIDs)
  isplitr
  · ipureintro; rfl
  iintro %s ⟨S, -⟩
  wp_auto
  iapply HΦ $$ S

theorem promreg.wp_BuiltinDims :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.promreg }}
      (App (Val (@! promreg.BuiltinDims)) (Val #()))
    {{ (s : GoSlice), RET #s; s ↦* promreg.builtinDims }} := by
  wp_start
  wp_auto
  wp_apply wp_slice_literal (l := promreg.builtinDims)
  isplitr
  · ipureintro; rfl
  iintro %s ⟨S, -⟩
  wp_auto
  iapply HΦ $$ S

theorem promreg.wp_BuiltinNames :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.promreg }}
      (App (Val (@! promreg.BuiltinNames)) (Val #()))
    {{ (s : GoSlice), RET #s; s ↦* promreg.builtinNames }} := by
  wp_start
  wp_auto
  wp_apply wp_slice_literal (l := promreg.builtinNames)
  isplitr
  · ipureintro; rfl
  iintro %s ⟨S, -⟩
  wp_auto
  iapply HΦ $$ S

theorem promreg.wp_BuiltinCollectors :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.promreg }}
      (App (Val (@! promreg.BuiltinCollectors)) (Val #()))
    {{ (s : GoSlice), RET #s; s ↦* promreg.builtinCollectors }} := by
  wp_start
  wp_auto
  wp_apply wp_slice_literal (l := promreg.builtinCollectors)
  isplitr
  · ipureintro; rfl
  iintro %s ⟨S, -⟩
  wp_auto
  iapply HΦ $$ S

theorem promreg.Registry.SeedBuiltins.wp_proof : promreg.Registry.SeedBuiltins.spec (GF := GF) (hG := hG) := by
  intro f r
  wp_start as ⟨#Hreg, Htoks⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold promreg.isRegistry at Hreg
  icases Hreg with ⟨%mI, %mD, %mC, #HI, #HD, #HC, #Hmu⟩
  wp_auto
  wp_apply (sync.Mutex.wp_Lock _ _) $$ [] as ⟨Hlk, HR⟩
  · iframe #
  iunfold promreg.regInv at HR
  icases HR with ⟨%ids, %dims, %cols, HmI, HmD, HmC, Hrt, %Hp⟩
  wp_apply promreg.wp_BuiltinIDs as %sI SI
  ihave %HlenI := ownSlice_len _ _ _ $$ SI
  icases (promreg.builtinToks_split (GF := GF)).1 $$ Htoks with ⟨HtI, HtC⟩
  obtain ⟨Hids, Hcols, Hdims⟩ := Hp
  ihave Hinv : iprop(∃ (j : Nat) (ids' : GMap w64 Bool), "i" ∷ i_ptr ↦ W64 j ∗ "HmI" ∷ mI ↦$ ids' ∗
      "Hrt" ∷ ([∗map] k ↦ _b ∈ ids' ∪ cols, promreg.idTok (GF := GF) k) ∗
      "HtI" ∷ promreg.idToks (GF := GF) (promreg.builtinIDs.drop j) ∗ "id" ∷ (∃ v : w64, id_ptr ↦ v) ∗
      "%Hj" ∷ ⌜j ≤ promreg.builtinIDs.length ∧ (∀ k b, ids' !! k = some b → b = true) ∧
        (∀ n h, dims !! n = some h → n ∈ promreg.builtinNames ∨ ids' !! f n = some true)⌝) $$ [i HmI Hrt HtI id]
  · iexists 0, ids
    iframe
    isplitl [id]
    · iexists _; iexact id
    ipureintro; exact ⟨by decide, Hids, Hdims⟩
  wp_for Hinv
  obtain ⟨Hj, Hids', Hdims'⟩ := Hj
  by_cases hj : j < promreg.builtinIDs.length
  · have hc : sint.Z (W64 (j : Int)) < sint.Z sI.len := by
      have : promreg.builtinIDs.length = 38 := rfl
      word
    simp only [decide_eq_true hc, ↓reduceIte]
    wp_auto
    have h0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
    simp only [h0, hc, and_self, ↓reduceIte]
    have hsj : (sint.Z (W64 (j : Int))).toNat = j := by word
    obtain ⟨x, hx⟩ : ∃ x, promreg.builtinIDs[j]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
    icases id with ⟨%v, id⟩
    wp_apply (wp_load_slice_index (t := go.uint64) sI (sint.Z (W64 (j : Int))) promreg.builtinIDs (DFrac.own 1) x h0) $$ [SI] as SI
    · iframe; ipureintro; rw [hsj]; exact hx
    have hdrop : promreg.builtinIDs.drop j = x :: promreg.builtinIDs.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons hj]; congr; exact (List.getElem?_eq_some_iff.mp hx).2
    rw [hdrop]
    icases (promreg.idToks_cons (GF := GF) x _).1 $$ HtI with ⟨Hx, HtI⟩
    icases promreg.regToks_absent (GF := GF) _ x $$ [Hrt Hx] with ⟨%Hab, Hrt, Hx⟩
    · iframe
    have hx1 : ids' !! x = none := by
      rw [gmap_lookup_union] at Hab; cases h : ids' !! x <;> simp_all
    wp_apply wp_mapInsert $$ [$HmI] as HmI
    ihave Hrt := promreg.regToks_insert (GF := GF) _ x true Hab $$ [Hrt Hx]
    · iframe
    rw [← promreg.union_insert_l]
    iapply wp_for_post_do
    wp_auto
    iframe
    iexists (j + 1), <[x := true]> ids'
    have hw : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by word
    rw [hw]
    iframe
    isplitl [id]
    · iexists _; iexact id
    ipureintro
    refine ⟨hj, fun k b hk => ?_, fun n h hn => ?_⟩
    · by_cases e : x = k
      · subst e; rw [GMap.lookup_insert] at hk; cases hk; rfl
      · rw [GMap.lookup_insert_ne _ _ e] at hk; exact Hids' k b hk
    · rcases Hdims' n h hn with h1 | h1
      · exact Or.inl h1
      · right
        by_cases e : x = f n
        · rw [e, GMap.lookup_insert]
        · rw [GMap.lookup_insert_ne _ _ e]; exact h1
  · have hc : ¬ sint.Z (W64 (j : Int)) < sint.Z sI.len := by
      have : promreg.builtinIDs.length = 38 := rfl
      word
    simp only [decide_eq_false hc, Bool.false_eq_true, ↓reduceIte]
    have hjl : j = promreg.builtinIDs.length := by omega
    subst hjl
    wp_auto
    wp_apply promreg.wp_BuiltinDims as %sD SD
    wp_apply promreg.wp_BuiltinNames as %sN SN
    ihave %HlenN := ownSlice_len _ _ _ $$ SN
    ihave %HlenD := ownSlice_len _ _ _ $$ SD
    rename_i iv_ptr
    irename : (iv_ptr ↦ (zero_val w64) : IProp GF) => iv
    have hND : promreg.builtinNames.length = 38 := rfl
    have hDD : promreg.builtinDims.length = 38 := rfl
    have hsN : sint.Z sN.len = 38 := by have h := HlenN.1; rw [hND] at h; word
    have hsD : sint.Z sD.len = 38 := by have h := HlenD.1; rw [hDD] at h; word
    ihave Hinv : iprop(∃ (j : Nat) (dims' : GMap GoString w64), "i" ∷ i_ptr ↦ W64 j ∗ "HmD" ∷ mD ↦$ dims' ∗
      "n" ∷ (∃ v : GoString, n_ptr ↦ v) ∗ "iv" ∷ (∃ v : w64, iv_ptr ↦ v) ∗
      "%Hj" ∷ ⌜j ≤ promreg.builtinNames.length ∧
        (∀ n h, dims' !! n = some h → n ∈ promreg.builtinNames ∨ ids' !! f n = some true)⌝) $$ [i HmD n iv]
    · iexists 0, dims
      iframe
      isplitl [n]
      · iexists _; iexact n
      isplitl [iv]
      · iexists _; iexact iv
      ipureintro; exact ⟨by decide, Hdims'⟩
    wp_for Hinv
    obtain ⟨Hj, Hdims''⟩ := Hj
    by_cases hj : j < promreg.builtinNames.length
    · have hj38 : j < 38 := hND ▸ hj
      have hc : sint.Z (W64 (j : Int)) < sint.Z sN.len := by rw [hsN]; word
      simp only [decide_eq_true hc, ↓reduceIte]
      wp_auto
      have h0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
      simp only [h0, hc, and_self, ↓reduceIte]
      have hsj : (sint.Z (W64 (j : Int))).toNat = j := by word
      obtain ⟨x, hx⟩ : ∃ x, promreg.builtinNames[j]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
      obtain ⟨d, hd⟩ : ∃ d, promreg.builtinDims[j]? = some d :=
        ⟨_, List.getElem?_eq_getElem (by rw [hDD]; rw [hND] at hj; exact hj)⟩
      icases n with ⟨%vn, n⟩
      icases iv with ⟨%vi, iv⟩
      wp_apply (wp_load_slice_index (t := go.string) sN (sint.Z (W64 (j : Int))) promreg.builtinNames (DFrac.own 1) x h0) $$ [SN] as SN
      · iframe; ipureintro; rw [hsj]; exact hx
      have hcD : sint.Z (W64 (j : Int)) < sint.Z sD.len := by rw [hsD]; word
      simp only [h0, hcD, and_self, ↓reduceIte]
      wp_apply (wp_load_slice_index (t := go.uint64) sD (sint.Z (W64 (j : Int))) promreg.builtinDims (DFrac.own 1) d h0) $$ [SD] as SD
      · iframe; ipureintro; rw [hsj]; exact hd
      wp_apply wp_mapInsert $$ [$HmD] as HmD
      iapply wp_for_post_do
      wp_auto
      iframe
      iexists (j + 1), <[x := d]> dims'
      have hw : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by word
      rw [hw]
      iframe
      isplitl [n]
      · iexists _; iexact n
      isplitl [iv]
      · iexists _; iexact iv
      ipureintro
      refine ⟨hj, fun n h hn => ?_⟩
      by_cases e : x = n
      · subst e; exact Or.inl (List.mem_of_getElem? hx)
      · rw [GMap.lookup_insert_ne _ _ e] at hn; exact Hdims'' n h hn
    · have hj38 : j = 38 := by rw [hND] at hj Hj; omega
      have hc : ¬ sint.Z (W64 (j : Int)) < sint.Z sN.len := by rw [hsN, hj38]; decide
      simp only [decide_eq_false hc, Bool.false_eq_true, ↓reduceIte]
      wp_auto
      wp_apply promreg.wp_BuiltinCollectors as %sC SC
      ihave %HlenC := ownSlice_len _ _ _ $$ SC
      have hCC : promreg.builtinCollectors.length = 2 := rfl
      have hsC : sint.Z sC.len = 2 := by have h := HlenC.1; rw [hCC] at h; word
      ihave Hinv : iprop(∃ (j : Nat) (cols' : GMap w64 Bool), "i" ∷ i_ptr ↦ W64 j ∗ "HmC" ∷ mC ↦$ cols' ∗
          "Hrt" ∷ ([∗map] k ↦ _b ∈ ids' ∪ cols', promreg.idTok (GF := GF) k) ∗
          "HtC" ∷ promreg.idToks (GF := GF) (promreg.builtinCollectors.drop j) ∗ "c" ∷ (∃ v : w64, c_ptr ↦ v) ∗
          "%Hj" ∷ ⌜j ≤ promreg.builtinCollectors.length ∧ (∀ k b, cols' !! k = some b → b = true)⌝)
        $$ [i HmC Hrt HtC c]
      · iexists 0, cols
        iframe
        isplitl [c]
        · iexists _; iexact c
        ipureintro; exact ⟨by decide, Hcols⟩
      wp_for Hinv
      obtain ⟨Hj, Hcols'⟩ := Hj
      by_cases hj : j < promreg.builtinCollectors.length
      · have hc : sint.Z (W64 (j : Int)) < sint.Z sC.len := by rw [hsC]; rw [hCC] at hj; word
        simp only [decide_eq_true hc, ↓reduceIte]
        wp_auto
        have h0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
        simp only [h0, hc, and_self, ↓reduceIte]
        have hsj : (sint.Z (W64 (j : Int))).toNat = j := by word
        obtain ⟨x, hx⟩ : ∃ x, promreg.builtinCollectors[j]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
        icases c with ⟨%v, c⟩
        wp_apply (wp_load_slice_index (t := go.uint64) sC (sint.Z (W64 (j : Int))) promreg.builtinCollectors (DFrac.own 1) x h0) $$ [SC] as SC
        · iframe; ipureintro; rw [hsj]; exact hx
        have hdrop : promreg.builtinCollectors.drop j = x :: promreg.builtinCollectors.drop (j + 1) := by
          rw [List.drop_eq_getElem_cons hj]; congr; exact (List.getElem?_eq_some_iff.mp hx).2
        rw [hdrop]
        icases (promreg.idToks_cons (GF := GF) x _).1 $$ HtC with ⟨Hx, HtC⟩
        icases promreg.regToks_absent (GF := GF) _ x $$ [Hrt Hx] with ⟨%Hab, Hrt, Hx⟩
        · iframe
        have hx1 : ids' !! x = none := by
          rw [gmap_lookup_union] at Hab; cases h : ids' !! x <;> simp_all
        wp_apply wp_mapInsert $$ [$HmC] as HmC
        ihave Hrt := promreg.regToks_insert (GF := GF) _ x true Hab $$ [Hrt Hx]
        · iframe
        rw [← promreg.union_insert_r _ _ _ _ hx1]
        iapply wp_for_post_do
        wp_auto
        iframe
        iexists (j + 1), <[x := true]> cols'
        have hw : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by word
        rw [hw]
        iframe
        isplitl [c]
        · iexists _; iexact c
        ipureintro
        refine ⟨hj, fun k b hk => ?_⟩
        by_cases e : x = k
        · subst e; rw [GMap.lookup_insert] at hk; cases hk; rfl
        · rw [GMap.lookup_insert_ne _ _ e] at hk; exact Hcols' k b hk
      · have hj2 : j = 2 := by rw [hCC] at hj Hj; omega
        have hc : ¬ sint.Z (W64 (j : Int)) < sint.Z sC.len := by rw [hsC, hj2]; decide
        simp only [decide_eq_false hc, Bool.false_eq_true, ↓reduceIte]
        wp_auto
        wp_apply (sync.Mutex.wp_Unlock _ _) $$ [Hlk HmI HmD HmC Hrt]
        · iframe #
          iframe Hlk
          inext
          iunfold promreg.regInv
          iexists ids', dims', cols'
          iframe
          ipureintro
          exact ⟨Hids', Hcols', Hdims''⟩
        iapply HΦ
        itrivial

end proof

end EtcdGrove
end Perennial
