module
public import Spec.go_etcd_io.bbolt.node__put
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Spec.go_etcd_io.bbolt.internal.common.Inode__SetFlags
public import Spec.go_etcd_io.bbolt.internal.common.Inode__SetKey
public import Spec.go_etcd_io.bbolt.internal.common.Inode__SetValue
public import Spec.go_etcd_io.bbolt.internal.common.Inode__SetPgid
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Pgid
public import Spec.go_etcd_io.bbolt.internal.common.Assert

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

theorem node.put.wp_proof (hPgid : _root_.Perennial.EtcdGrove.bbolt.Meta.Pgid.spec (GF := GF) (hG := hG))
    (hK : Inode.Key.spec (GF := GF) (hG := hG))
    (hSF : Inode.SetFlags.spec (GF := GF) (hG := hG))
    (hSK : Inode.SetKey.spec (GF := GF) (hG := hG))
    (hSV : Inode.SetValue.spec (GF := GF) (hG := hG))
    (hSP : Inode.SetPgid.spec (GF := GF) (hG := hG))
    (hA : Assert.spec (GF := GF) (hG := hG)) :
    node.put.spec (GF := GF) (hG := hG) := by
  intro nl nv ins es bv dqb tv dqt mv dqm oldKey okb dok newKey nkb dnk value vb dv pgId flags
    Hsorted Hpg Hok Hnk
  wp_start as ⟨Hn, Hs, Hcap, Ho, Hb, Ht, Hm, Hokp, Hnkp, Hvp⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave %Hol := inodesOwn_length _ _ $$ Ho
  ihave %Hcw := ownSliceCap_wf _ _ $$ Hcap
  ihave %Hokl := ownSlice_len _ _ _ $$ Hokp
  ihave %Hnkl := ownSlice_len _ _ _ $$ Hnkp
  wp_auto
  wp_apply hPgid $$ [$Hm] as Hm
  try wp_auto
  wp_if_destruct
  · exfalso; word
  wp_if_destruct
  · exfalso; word
  wp_if_destruct
  · exfalso; word
  have Hlen : sint.Z nv.inodes'.len = (es.length : Int) := by word
  wp_apply sort.wp_Search nv.inodes'.len _ (entryGE es okb)
    iprop(n_ptr ↦ nl ∗ oldKey_ptr ↦ oldKey ∗ nl ↦ nv ∗ nv.inodes' ↦* ins ∗ inodesOwn ins es ∗
      oldKey ↦*{dok} okb) $$ [n oldKey Hn Hs Ho Hokp]
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
    ipureintro; rw [Hlen]; exact entryGE_mono es okb Hsorted
  iintro %idx ⟨⟨Hnp, Hkp, Hn, Hs, Ho, Hokp⟩, %H0, %Hfound, %Hoob, %Hgt⟩
  rw [Hlen] at Hfound Hoob
  have Hsi := isSearchIdx_of_search es okb idx H0 Hfound Hoob Hgt
  try wp_auto
  ispecialize HΦ $$ %idx
  wp_join (Q := fun v => iprop(⌜v = #(decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = okb))⌝ ∗
      n_ptr ↦ nl ∗ oldKey_ptr ↦ oldKey ∗ index_ptr ↦ idx ∗ nl ↦ nv ∗ nv.inodes' ↦* ins ∗
      inodesOwn ins es ∗ oldKey ↦*{dok} okb))
    at (if: _ then _ else _) with [Hnp Hkp index Hn Hs Ho Hokp] as ⟨%Hv, Hnp, Hkp, index, Hn, Hs, Ho, Hokp⟩
  · wp_if_destruct
    · wp_if_destruct
      · have Hlt : sint.nat idx < es.length := by word
        list_elem ins (sint.nat idx) as it
        list_elem es (sint.nat idx) as e
        rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z idx ∧ sint.Z idx < sint.Z nv.inodes'.len
          from ⟨H0, by word⟩))]
        icases ownSlice_elem_acc (sint.Z idx) it _ _ ins H0 Hit_lookup $$ Hs with ⟨Hit, Hsback⟩
        wp_apply hK $$ [$Hit] as Hit
        try wp_auto
        icases inodesOwn_key_acc _ _ _ it e Hit_lookup He_lookup $$ Ho with ⟨Hik, Hoback⟩
        wp_apply bytes.wp_Equal _ _ _ _ _ _ $$ [Hik Hokp] as ⟨Hik, Hokp⟩
        · iframe
        ispecialize Hoback $$ Hik
        ihave Hs := Hsback $$ Hit
        rw [list_set_lookup_self _ _ _ Hit_lookup]
        have Hek : entryKey es (sint.nat idx) = e.key := by
          unfold entryKey; rw [He_lookup]; rfl
        iframe
        ipureintro
        congr 1
        exact decide_eq_decide.mpr ⟨fun h => ⟨Hlt, by rw [Hek]; exact h⟩, fun h => by rw [← Hek]; exact h.2⟩
      · iframe
        ipureintro
        congr 1
        exact (decide_eq_false (fun h => by have := h.1; word)).symm
    · iframe
      ipureintro
      congr 1
      exact (decide_eq_false (fun h => by have := h.1; word)).symm
  subst Hv
  have Hpi := (decide_eq_true_iff (p := sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = okb))
  generalize Hex : decide (sint.nat idx < es.length ∧ entryKey es (sint.nat idx) = okb) = ex at Hpi ⊢
  wp_auto
  wp_join iprop(∃ (s' : GoSlice) (L : List internal.common.Inode),
      n_ptr ↦ nl ∗ index_ptr ↦ idx ∗ nl ↦ ({ nv with inodes' := s' } : node) ∗ s' ↦* L ∗
      ownSliceCap internal.common.Inode s' (DFrac.own 1) ∗
      ⌜sint.nat idx < L.length ∧
        ∀ x, L.set (sint.nat idx) x = putList ins (sint.nat idx) ex x⌝)
    at next with [Hn Hs Hcap Hnp index] as ⟨%s', %L, Hnp, index, Hn, Hs, Hcap, %HL⟩
  · have Hile : sint.nat idx ≤ ins.length := by have := Hsi.1; omega
    cases ex
    · try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl] as %s1 ⟨Hs, Hcap, -⟩
      try wp_auto
      ihave %Hsl1 := ownSlice_len _ _ _ $$ Hs
      ihave %Hcw1 := ownSliceCap_wf _ _ $$ Hcap
      simp only [List.length_append, List.length_singleton] at Hsl1
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (idx + W64 1) ∧
        sint.Z (idx + W64 1) ≤ sint.Z s1.len ∧ sint.Z s1.len ≤ sint.Z s1.cap from
        ⟨by word, by word, Hcw1.2⟩))]
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z idx ∧
        sint.Z idx ≤ sint.Z s1.len ∧ sint.Z s1.len ≤ sint.Z s1.cap from
        ⟨H0, by word, Hcw1.2⟩))]
      try wp_auto
      wp_apply wp_slice_copy_within s1 _ (idx + W64 1) s1.len idx s1.len
        ⟨by word, by word, by word⟩ ⟨H0, by word, by word⟩ $$ [Hs] as %n ⟨_, Hs⟩
      · iframe
      try wp_auto
      rw [show sint.nat (idx + W64 1) = sint.nat idx + 1 by word,
        show sint.nat s1.len = ins.length + 1 by omega]
      isplitl []
      · ipureintro; rfl
      iexists s1, _
      iframe
      ipureintro
      have Hset := fun x => insert_copy_list ins (zero_val internal.common.Inode) x (sint.nat idx) Hile
      refine ⟨?_, fun x => by rw [Hset x]; rfl⟩
      have := congrArg List.length (Hset (zero_val internal.common.Inode))
      rw [List.length_set] at this
      rw [this]
      simp only [List.length_append, List.length_take, List.length_cons, List.length_drop]
      omega
    · try wp_auto
      isplitl []
      · ipureintro; rfl
      iexists nv.inodes', ins
      iframe
      ipureintro
      exact ⟨by have := (Hpi.1 rfl).1; omega, fun x => rfl⟩
  have Hile : sint.nat idx ≤ ins.length := by have := Hsi.1; omega
  ihave %HsL := ownSlice_len _ _ _ $$ Hs
  list_elem L (sint.nat idx) as y
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z idx ∧ sint.Z idx < sint.Z s'.len from
    ⟨H0, by word⟩))]
  icases ownSlice_elem_acc (sint.Z idx) y _ _ L H0 Hy_lookup $$ Hs with ⟨Hit, Hsback⟩
  try wp_auto
  wp_apply hSF $$ [$Hit] as Hit
  try wp_auto
  wp_apply hSK $$ [$Hit] as Hit
  try wp_auto
  wp_apply hSV $$ [$Hit] as Hit
  try wp_auto
  wp_apply hSP $$ [$Hit] as Hit
  try wp_auto
  wp_apply hK $$ [$Hit] as Hit
  try wp_auto
  rw [decide_eq_true (show sint.Z (W64 0) < sint.Z newKey.len by word)]
  wp_apply hA
  try wp_auto
  try simp only
  ihave Hs := Hsback $$ Hit
  rw [show (sint.Z idx).toNat = sint.nat idx from rfl, HL.2]
  ispecialize HΦ $$ %s'
  cases ex
  · unfold putList
    simp only [Bool.false_eq_true, ↓reduceIte]
    ihave Ho := inodesOwn_insert ins es (sint.nat idx) (internal.common.Inode.mk flags pgId newKey value)
      (NodeEntry.mk flags pgId nkb vb dnk dv) Hol Hile $$ [Ho Hnkp Hvp]
    · iframe
      unfold inodeIs
      iframe
      ipureintro; exact ⟨rfl, rfl⟩
    iapply HΦ
    iframe
    ipureintro; exact ⟨H0, Hsi⟩
  · obtain ⟨Hlt, Hek⟩ := Hpi.1 rfl
    list_elem ins (sint.nat idx) as it
    list_elem es (sint.nat idx) as e
    unfold putList
    simp only [↓reduceIte]
    icases inodesOwn_replace ins es (sint.nat idx) it e (internal.common.Inode.mk flags pgId newKey value)
      (NodeEntry.mk flags pgId nkb vb dnk dv) Hit_lookup He_lookup $$ [Ho Hnkp Hvp] with ⟨Ho, Hold⟩
    · iframe
      unfold inodeIs
      iframe
      ipureintro; exact ⟨rfl, rfl⟩
    iapply HΦ
    iframe
    isplitl []
    · ipureintro; exact ⟨H0, Hsi⟩
    ipureintro; exact ⟨Hit_lookup, He_lookup⟩

end proof

end bbolt
end EtcdGrove
end Perennial
