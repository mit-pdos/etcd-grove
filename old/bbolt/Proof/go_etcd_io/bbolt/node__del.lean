module
public import Spec.go_etcd_io.bbolt.node__del
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Proof.go_etcd_io.bbolt.SliceWithin

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem node.del.wp_proof (hK : Inode.Key.spec (GF := GF) (hG := hG)) :
    node.del.spec (GF := GF) (hG := hG) := by
  intro nl nv ins es key kb dk Hsorted
  wp_start as ⟨Hn, Hs, Hcap, Ho, Hk⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave %Hol := inodesOwn_length _ _ $$ Ho
  ihave %Hcw := ownSliceCap_wf _ _ $$ Hcap
  wp_auto
  have Hlen : sint.Z nv.inodes'.len = (es.length : Int) := by word
  wp_apply sort.wp_Search nv.inodes'.len _ (entryGE es kb)
    iprop(n_ptr ↦ nl ∗ key_ptr ↦ key ∗ nl ↦ nv ∗ nv.inodes' ↦* ins ∗ inodesOwn ins es ∗
      key ↦*{dk} kb) $$ [n key Hn Hs Ho Hk]
  · iframe
    isplitl []
    · ipureintro; word
    isplitl []
    · unfold sort.predImplements
      iintro %i
      wp_start as ⟨⟨Hnp, Hkp, Hn, Hs, Ho, Hk⟩, %Hb⟩
      wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hb.1, Hb.2⟩)]
      list_elem ins (sint.Z i).toNat as it
      list_elem es (sint.Z i).toNat as e
      icases ownSlice_elem_acc (sint.Z i) it _ _ ins Hb.1 Hit_lookup $$ Hs with ⟨Hit, Hsback⟩
      wp_apply hK $$ [$Hit] as Hit
      try wp_auto
      icases inodesOwn_key_acc _ _ _ it e Hit_lookup He_lookup $$ Ho with ⟨Hik, Hoback⟩
      wp_apply bytes.wp_Compare _ _ _ _ _ _ $$ [Hik Hk] as ⟨Hik, Hk⟩
      · iframe
      try wp_auto
      ispecialize Hoback $$ Hik
      ihave Hs := Hsback $$ Hit
      rw [list_set_lookup_self _ _ _ Hit_lookup]
      iapply HΦ
      iframe
      ipureintro
      have Hek : entryKey es (sint.Z i).toNat = e.key := by
        unfold entryKey; rw [He_lookup]; rfl
      simp only [entryGE, Hek, ne_eq, ← decide_not]
    ipureintro; rw [Hlen]; exact entryGE_mono es kb Hsorted
  iintro %idx ⟨⟨Hnp, Hkp, Hn, Hs, Ho, Hk⟩, %H0, %Hfound, %Hoob, %Hgt⟩
  rw [Hlen] at Hfound Hoob
  have Hsi := isSearchIdx_of_search es kb idx H0 Hfound Hoob Hgt
  try wp_auto
  ispecialize HΦ $$ %idx
  wp_if_destruct
  · -- past the end: not found
    have Hnf : ¬ (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = kb) := by
      intro h; have := h.1; word
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by simpa using Hnf))]
    iapply HΦ
    iframe
    ipureintro; exact ⟨H0, Hsi⟩
  · have Hlt : sint.nat idx < es.length := by word
    list_elem ins (sint.nat idx) as it
    list_elem es (sint.nat idx) as e
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z idx ∧ sint.Z idx < sint.Z nv.inodes'.len from ⟨H0, by word⟩))]
    icases ownSlice_elem_acc (sint.Z idx) it _ _ ins H0 Hit_lookup $$ Hs with ⟨Hit, Hsback⟩
    wp_apply hK $$ [$Hit] as Hit
    try wp_auto
    icases inodesOwn_key_acc _ _ _ it e Hit_lookup He_lookup $$ Ho with ⟨Hik, Hoback⟩
    wp_apply bytes.wp_Equal _ _ _ _ _ _ $$ [Hik Hk] as ⟨Hik, Hk⟩
    · iframe
    ispecialize Hoback $$ Hik
    ihave Hs := Hsback $$ Hit
    rw [list_set_lookup_self _ _ _ Hit_lookup]
    have Hek : entryKey es (sint.nat idx) = e.key := by
      unfold entryKey; rw [He_lookup]; rfl
    by_cases Heq : e.key = kb
    · rw [decide_eq_true Heq]
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z idx ∧
        sint.Z idx ≤ sint.Z nv.inodes'.cap from ⟨by decide, H0, by word⟩))]
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (idx + W64 1) ∧
        sint.Z (idx + W64 1) ≤ sint.Z nv.inodes'.len ∧ sint.Z nv.inodes'.len ≤ sint.Z nv.inodes'.cap
        from ⟨by word, by word, by word⟩))]
      try wp_auto
      wp_apply wp_slice_append_delete (st := internal.common.Inodes.ty) nv.inodes' ins idx
        ⟨H0, by word⟩ $$ [Hs Hcap] as ⟨Hs, Hcap⟩
      · iframe
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (by simp [Hek, Heq, Hlt]))]
      have Hil : sint.nat idx < ins.length := by omega
      icases (inodesOwn_split ins es (sint.nat idx) it e Hit_lookup He_lookup).1 $$ Hoback
        with ⟨Ha, Hie, Hb⟩
      ihave Ho := (inodesOwn_app (ins.take (sint.nat idx)) (ins.drop (sint.nat idx + 1))
        (es.take (sint.nat idx)) (es.drop (sint.nat idx + 1)) (by simp only [List.length_take]; omega)).2
        $$ [Ha Hb]
      · iframe
      rw [← List.eraseIdx_eq_take_drop_succ, ← List.eraseIdx_eq_take_drop_succ]
      iapply HΦ
      iframe
      isplitl []
      · ipureintro; exact ⟨H0, Hsi⟩
      ipureintro; exact ⟨Hit_lookup, He_lookup⟩
    · rw [decide_eq_false Heq]
      try wp_auto
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by simp [Hek, Heq]))]
      iapply HΦ
      iframe
      ipureintro; exact ⟨H0, Hsi⟩

end proof

end bbolt
end EtcdGrove
end Perennial
