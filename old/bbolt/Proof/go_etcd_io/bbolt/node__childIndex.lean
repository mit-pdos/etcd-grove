module
public import Spec.go_etcd_io.bbolt.node__childIndex
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key

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

theorem node.childIndex.wp_proof (hK : Inode.Key.spec (GF := GF) (hG := hG)) :
    node.childIndex.spec (GF := GF) (hG := hG) := by
  intro nl nv dq ins dqs es cl cv dqc ck dk Hsorted
  wp_start as ⟨Hn, Hs, Ho, Hc, Hck⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave %Hol := inodesOwn_length _ _ $$ Ho
  wp_auto
  have Hlen : sint.Z nv.inodes'.len = (es.length : Int) := by word
  wp_apply sort.wp_Search nv.inodes'.len _ (entryGE es ck)
    iprop(n_ptr ↦ nl ∗ child_ptr ↦ cl ∗ nl ↦{dq} nv ∗ nv.inodes' ↦*{dqs} ins ∗ inodesOwn ins es ∗
      cl ↦{dqc} cv ∗ cv.key' ↦*{dk} ck) $$ [n child Hn Hs Ho Hc Hck]
  · iframe
    isplitl []
    · ipureintro; word
    isplitl []
    · unfold sort.predImplements
      iintro %i
      wp_start as ⟨⟨Hnp, Hcp, Hn, Hs, Ho, Hc, Hck⟩, %Hb⟩
      wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hb.1, Hb.2⟩)]
      list_elem ins (sint.Z i).toNat as it
      list_elem es (sint.Z i).toNat as e
      icases ownSlice_elem_acc (sint.Z i) it _ _ ins Hb.1 Hit_lookup $$ Hs with ⟨Hit, Hsback⟩
      wp_apply hK $$ [$Hit] as Hit
      try wp_auto
      icases inodesOwn_key_acc _ _ _ it e Hit_lookup He_lookup $$ Ho with ⟨Hk, Hoback⟩
      wp_apply bytes.wp_Compare _ _ _ _ _ _ $$ [Hk Hck] as ⟨Hk, Hck⟩
      · iframe
      try wp_auto
      ispecialize Hoback $$ Hk
      ihave Hs := Hsback $$ Hit
      rw [list_set_lookup_self _ _ _ Hit_lookup]
      iapply HΦ
      iframe
      ipureintro
      have Hek : entryKey es (sint.Z i).toNat = e.key := by
        unfold entryKey; rw [He_lookup]; rfl
      simp only [entryGE, Hek, ne_eq, ← decide_not]
    ipureintro; rw [Hlen]; exact entryGE_mono es ck Hsorted
  iintro %idx ⟨⟨Hnp, Hcp, Hn, Hs, Ho, Hc, Hck⟩, %H0, %Hfound, %Hoob, %Hgt⟩
  rw [Hlen] at Hfound Hoob
  have Hsi := isSearchIdx_of_search es ck idx H0 Hfound Hoob Hgt
  try wp_auto
  ispecialize HΦ $$ %idx
  iapply HΦ
  iframe
  ipureintro
  exact ⟨H0, Hsi⟩

end proof

end bbolt
end EtcdGrove
end Perennial
