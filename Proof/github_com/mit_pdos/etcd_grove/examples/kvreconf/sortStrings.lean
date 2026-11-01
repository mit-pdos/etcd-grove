/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/sortStrings.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.sortStrings
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.less

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]

/-- Swapping two adjacent elements permutes. -/
theorem perm_swap_adj {α : Type} (zs : List α) (j : Nat) (a b : α) (hj : 0 < j)
    (ha : zs[j - 1]? = some a) (hb : zs[j]? = some b) :
    ((zs.set j a).set (j - 1) b).Perm zs := by
  have hjl : j < zs.length := (List.getElem?_eq_some_iff.1 hb).1
  obtain ⟨l1, l2, rfl, hl1⟩ : ∃ l1 l2, zs = l1 ++ a :: b :: l2 ∧ l1.length = j - 1 := by
    refine ⟨zs.take (j - 1), zs.drop (j + 1), ?_, by simp; omega⟩
    have h1 : zs.drop (j - 1) = zs[j - 1] :: zs.drop (j - 1 + 1) :=
      List.drop_eq_getElem_cons (by omega)
    rw [show j - 1 + 1 = j by omega] at h1
    have h2 : zs.drop j = zs[j] :: zs.drop (j + 1) := List.drop_eq_getElem_cons hjl
    have ea : zs[j - 1] = a := by rw [List.getElem?_eq_getElem (by omega)] at ha; exact Option.some.inj ha
    have eb : zs[j] = b := by rw [List.getElem?_eq_getElem hjl] at hb; exact Option.some.inj hb
    conv => lhs; rw [← List.take_append_drop (j - 1) zs]
    rw [h1, h2, ea, eb]
  have hj1 : j = l1.length + 1 := by omega
  subst hj1
  simp only [Nat.add_sub_cancel]
  rw [List.set_append_right _ _ (by omega), List.set_append_right _ _ (by omega)]
  simp only [Nat.add_sub_cancel_left, Nat.sub_self, List.set_cons_succ, List.set_cons_zero]
  exact List.Perm.append_left _ (List.Perm.swap _ _ _)

theorem sortStrings.wp_proof (wp_less : less.spec (GF := GF) (hG := hG)) :
    sortStrings.spec (GF := GF) (hG := hG) := by
  intro ks xs
  wp_start as Hks
  try wp_auto
  ihave HI : (∃ (i : w64) (ys : List GoString), "i" ∷ i_ptr ↦ i ∗ "Hks" ∷ ks ↦* ys ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ ys.Perm xs⌝ : IProp GF) $$ [i Hks]
  · iexists W64 1, xs
    iframe
    ipureintro; exact ⟨by decide, List.Perm.refl _⟩
  wp_for HI
  ihave %Hl := ownSlice_len _ _ _ $$ Hks
  try wp_auto
  wp_if_destruct
  · try wp_auto
    ihave HJ : (∃ (jv : w64) (zs : List GoString), "j" ∷ j_ptr ↦ jv ∗ "Hks" ∷ ks ↦* zs ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z jv ∧ sint.Z jv < sint.Z ks.len ∧ zs.Perm xs⌝ : IProp GF) $$ [j Hks]
    · iexists i, ys
      iframe
      ipureintro; exact ⟨Hi.1, Hif, Hi.2⟩
    wp_for HJ
    ihave %Hl2 := ownSlice_len _ _ _ $$ Hks
    try wp_auto
    have Hft : ¬ ((#false : val) = #true) := fun h => Bool.false_ne_true (go.intoVal_inj h)
    wp_if_destruct
    · have Hj0 : 0 < sint.Z jv := Hif
      have Hjl : sint.nat jv < zs.length := by word
      obtain ⟨a, Ha⟩ : ∃ a, zs[sint.nat jv]? = some a := ⟨_, List.getElem?_eq_getElem Hjl⟩
      obtain ⟨b, Hb⟩ : ∃ b, zs[sint.nat jv - 1]? = some b :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have Hjm : sint.Z (jv - W64 1) = sint.Z jv - 1 := by word
      have Hjn : (sint.Z jv).toNat = sint.nat jv := rfl
      have Hjmn : (sint.Z (jv - W64 1)).toNat = sint.nat jv - 1 := by word
      try wp_auto
      rw [ite_eq_left (by omega)]
      wp_apply wp_load_slice_index ks (sint.Z jv) zs (DFrac.own 1) a Hj.1 $$ [$Hks] as Hks
      · ipureintro; rw [Hjn]; exact Ha
      try wp_auto
      rw [ite_eq_left (by omega)]
      wp_apply wp_load_slice_index ks (sint.Z (jv - W64 1)) zs (DFrac.own 1) b (by omega) $$ [$Hks]
        as Hks
      · ipureintro; rw [Hjmn]; exact Hb
      wp_apply wp_less a b as %c -
      cases c
      · rw [decide_eq_false Hft]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [if_pos (by simp)]
        wp_for_post
        iframe
        iexists i + W64 1, zs
        iframe
        ipureintro; exact ⟨by word, Hj.2.2⟩
      · rw [if_pos (by simp)]
        try wp_auto
        rw [ite_eq_left (by omega)]
        try wp_auto
        rw [ite_eq_left (by omega)]
        try wp_auto
        rw [ite_eq_left (by omega)]
        wp_apply wp_load_slice_index ks (sint.Z (jv - W64 1)) zs (DFrac.own 1) b (by omega) $$ [$Hks]
          as Hks
        · ipureintro; rw [Hjmn]; exact Hb
        try wp_auto
        rw [ite_eq_left (by omega)]
        wp_apply wp_load_slice_index ks (sint.Z jv) zs (DFrac.own 1) a Hj.1 $$ [$Hks] as Hks
        · ipureintro; rw [Hjn]; exact Ha
        try wp_auto
        wp_apply wp_store_slice_index ks (sint.Z jv) zs b $$ [$Hks] as Hks
        · ipureintro; omega
        try wp_auto
        wp_apply wp_store_slice_index ks (sint.Z (jv - W64 1)) (zs.set (sint.Z jv).toNat b) a $$ [$Hks]
          as Hks
        · ipureintro; simp only [List.length_set]; omega
        try wp_auto
        wp_for_post
        try wp_auto
        iframe
        iexists jv - W64 1, (zs.set (sint.nat jv) b).set (sint.nat jv - 1) a
        rw [Hjn, Hjmn]
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        exact (perm_swap_adj zs (sint.nat jv) b a (by word) Hb Ha).trans Hj.2.2
    · wp_for_post
      iframe
      iexists i + W64 1, zs
      iframe
      ipureintro; exact ⟨by word, Hj.2.2⟩
  · try wp_auto
    iapply HΦ
    iexists ys
    iframe
    ipureintro; exact Hi.2

end proof

end kvreconf
end EtcdGrove
end Perennial
