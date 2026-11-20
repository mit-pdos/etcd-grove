/-
`value.FieldList.Sort`: proved (Prove step, notes/smd-plan.md), over `sort.SliceStable`'s
trust-boundary spec (a hypothesis) and the premise of distinct names (post-freeze change B2c): the
slice ends at a sorted permutation, which with distinct names is `mergeSort`'s
(`ValuePure.eq_mergeSort_of_perm_sorted`); the two-item case swaps by hand.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.FieldList__Sort
public import Spec.sort.SliceStable
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsSort

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

theorem value.FieldList.Sort.wp_proof
    (h_sort_SliceStable : sort.SliceStable.spec (GF := GF) (hG := hG)) :
    value.FieldList.Sort.spec (GF := GF) := fun f fs => by
  wp_start as ⟨Hf, %Hnd, %Hlen⟩
  ihave %Hsl := ownSlice_len $$ Hf
  have hsorted : ∀ ys : List value.Field, ys.Perm fs →
      ys.Pairwise (fun a b => gsLt b.Name' a.Name' = false) →
      ys = fs.mergeSort (fun a b => !gsLt b.Name' a.Name') :=
    fun ys hp hs => ValuePure.eq_mergeSort_of_perm_sorted (·.Name') fs ys Hnd hp hs
  wp_auto
  wp_if_destruct
  · iapply HΦ
    rw [← hsorted fs (List.Perm.refl _) (by
      match fs, Hsl with
      | [], _ => simp
      | [_], _ => simp
      | _ :: _ :: _, Hsl => exfalso; simp at Hsl; word)]
    iexact Hf
  wp_if_destruct
  · obtain ⟨a, b, rfl⟩ : ∃ a b, fs = [a, b] := by
      match fs, Hsl with
      | [a, b], _ => exact ⟨a, b, rfl⟩
      | [], Hsl | [_], Hsl | _ :: _ :: _ :: _, Hsl => exfalso; rw [Hif, show sint.nat (W64 2) = 2 from rfl] at Hsl; simp at Hsl; try omega
    icases ownSlice_elem_acc 1 b f _ [a, b] (by omega) (by simp) $$ Hf with ⟨H1, Hf⟩
    have hz0 : sint.Z (W64 0) = 0 := rfl
    have hz1 : sint.Z (W64 1) = 1 := rfl
    have hl : sint.Z f.len = 2 := by rw [Hif]; rfl
    simp only [hz1, hl, Int.reduceLT, Int.reduceLE, _root_.and_self, ↓reduceIte]
    wp_auto
    ispecialize Hf $$ H1
    have hs1 : ([a, b] : List value.Field).set (Int.toNat 1) b = [a, b] := rfl
    simp only [hs1]
    icases ownSlice_elem_acc 0 a f _ [a, b] (by omega) (by simp) $$ Hf with ⟨H0, Hf⟩
    simp only [hz0, hl, Int.reduceLT, Int.reduceLE, _root_.and_self, ↓reduceIte]
    wp_auto
    ispecialize Hf $$ H0
    have hs0 : ([a, b] : List value.Field).set (Int.toNat 0) a = [a, b] := rfl
    simp only [hs0]
    wp_if_destruct
    · repeat (first | (simp only [hz0, hz1, hl, Int.reduceLT, Int.reduceLE, _root_.and_self,
          ↓reduceIte]; wp_auto))
      try simp only [hz0, hz1, hl, Int.reduceLT, Int.reduceLE, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index f 1 [a, b] _ b (by omega) $$ [Hf] as Hf
      · iframe; ipureintro; rfl
      repeat (first | (simp only [hz0, hz1, hl, Int.reduceLT, Int.reduceLE, _root_.and_self,
          ↓reduceIte]; wp_auto))
      try simp only [hz0, hz1, hl, Int.reduceLT, Int.reduceLE, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index f 0 [a, b] _ a (by omega) $$ [Hf] as Hf
      · iframe; ipureintro; rfl
      repeat (first | (simp only [hz0, hz1, hl, Int.reduceLT, Int.reduceLE, _root_.and_self,
          ↓reduceIte]; wp_auto))
      try simp only [hz0, hz1, hl, Int.reduceLT, Int.reduceLE, _root_.and_self, ↓reduceIte]
      wp_apply wp_store_slice_index f 0 [a, b] b $$ [Hf] as Hf
      · iframe; ipureintro; simp
      repeat (first | (simp only [hz0, hz1, hl, Int.reduceLT, Int.reduceLE, _root_.and_self,
          ↓reduceIte]; wp_auto))
      try simp only [hz0, hz1, hl, Int.reduceLT, Int.reduceLE, _root_.and_self, ↓reduceIte]
      wp_apply wp_store_slice_index f 1 _ a $$ [Hf] as Hf
      · iframe; ipureintro; simp
      repeat (first | (simp only [hz0, hz1, hl, Int.reduceLT, Int.reduceLE, _root_.and_self,
          ↓reduceIte]; wp_auto))
      try simp only [hz0, hz1, hl, Int.reduceLT, Int.reduceLE, _root_.and_self, ↓reduceIte]
      wp_auto
      have hsw : (([a, b] : List value.Field).set (Int.toNat 0) b).set (Int.toNat 1) a = [b, a] := rfl
      simp only [hsw]
      iapply HΦ
      have hba : gsLt b.Name' a.Name' = true := (ValuePure.goStringLt_iff_gsLt _ _).1 Hif
      have hab : gsLt a.Name' b.Name' = false := by
        cases h : gsLt a.Name' b.Name'
        · rfl
        · have := ValuePure.gsLt_trans hba h; rw [ValuePure.gsLt_irrefl] at this; cases this
      rw [← hsorted [b, a] (List.Perm.swap a b []) (by simp [hab])]
      iexact Hf
    · iapply HΦ
      have hba : gsLt b.Name' a.Name' = false := by
        cases h : gsLt b.Name' a.Name'
        · rfl
        · exact absurd ((ValuePure.goStringLt_iff_gsLt _ _).2 h) Hif
      rw [← hsorted [a, b] (List.Perm.refl _) (by simp [hba])]
      iexact Hf
  have hR : _root_.Perennial.slices.StrictWeakOrder
      (fun a b : value.Field => go.GoStringLt a.Name' b.Name') := by
    have h := _root_.Perennial.slices.StrictWeakOrder_goStringLt
    exact ⟨fun x => h.strict_weak_order_irrefl _,
      fun x y z => h.strict_weak_order_trans _ _ _,
      ⟨fun x => h.strict_weak_order_equiv.refl _, fun hxy => h.strict_weak_order_equiv.symm hxy,
        fun h1 h2 => h.strict_weak_order_equiv.trans h1 h2⟩⟩
  wp_apply h_sort_SliceStable (Et := value.Field.ty) (S := value.FieldList.ty)
    (fun a b : value.Field => go.GoStringLt a.Name' b.Name') f fs _ iprop(f_ptr ↦ f) hR
    $$ [$Hf $f] as ⟨%ys, Hf, f, %Hperm, %Hys⟩
  · isplitr
    · ipureintro; exact Hlen
    imodintro
    iintro %i %j %ys %yi %yj %Φ' %Hij Hs Hp HΦ'
    obtain ⟨hp, hi, hj, hi0, hj0⟩ := Hij
    ihave %Hl := ownSlice_len $$ Hs
    have hn : sint.nat f.len = (sint.Z f.len).toNat := rfl
    have hib : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z f.len := by
      have := (List.getElem?_eq_some_iff.1 hi).1; omega
    have hjb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z f.len := by
      have := (List.getElem?_eq_some_iff.1 hj).1; omega
    wp_auto
    simp only [hib, _root_.and_self, ↓reduceIte]
    icases ownSlice_elem_acc (sint.Z i) yi f _ ys hi0 hi $$ Hs with ⟨Hi, Hs⟩
    wp_auto
    ispecialize Hs $$ Hi
    simp only [list_set_lookup_self ys _ yi hi]
    simp only [hjb, _root_.and_self, ↓reduceIte]
    icases ownSlice_elem_acc (sint.Z j) yj f _ ys hj0 hj $$ Hs with ⟨Hj, Hs⟩
    wp_auto
    ispecialize Hs $$ Hj
    simp only [list_set_lookup_self ys _ yj hj]
    iapply HΦ' $$ %_ %(by simp) [$Hs] [$Hp]
  iapply HΦ
  rw [← hsorted ys Hperm ?_]
  · iexact Hf
  rw [List.pairwise_iff_getElem]
  intro k l hk hl hkl
  have h := Hys k l _ _ (List.getElem?_eq_getElem hk) (List.getElem?_eq_getElem hl) hkl
  cases h' : gsLt ys[l].Name' ys[k].Name'
  · rfl
  · exact absurd ((ValuePure.goStringLt_iff_gsLt _ _).2 h') h

end proof

end smd
end EtcdGrove
end Perennial
