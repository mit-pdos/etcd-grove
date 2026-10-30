module
public import Spec.go_etcd_io.bbolt.node__splitIndex
public import Spec.go_etcd_io.bbolt.node__pageElementSize
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Value

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

theorem node.splitIndex.wp_proof (hPE : node.pageElementSize.spec (GF := GF) (hG := hG))
    (hK : Inode.Key.spec (GF := GF) (hG := hG))
    (hV : Inode.Value.spec (GF := GF) (hG := hG)) :
    node.splitIndex.spec (GF := GF) (hG := hG) := by
  intro nl nv dq ins dqs thr
  wp_start as ⟨Hn, Hs⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  wp_auto
  unfold internal.common.PageHeaderSize internal.common.MinKeysPerPage
  wp_auto
  ihave IH : (∃ (j idx sz : w64),
      "i" ∷ i_ptr ↦ j ∗ "index" ∷ index_ptr ↦ idx ∗ "sz" ∷ sz_ptr ↦ sz ∗
      "Hs" ∷ nv.inodes' ↦*{dqs} ins ∗ "Hn" ∷ nl ↦{dq} nv ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ (0 < sint.Z j → sint.Z j ≤ sint.Z nv.inodes'.len - 2)⌝ ∗
      "%Hr" ∷ ⌜splitIndexOf thr ins =
        splitIndexGo thr (sint.nat j) idx sz ((ins.take (ins.length - 2)).drop (sint.nat j))⌝ :
        IProp GF) $$ [i index sz Hs Hn]
  · iexists W64 0, W64 0, W64 16
    simp only [named]
    rw [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
    iframe
    ipureintro; refine ⟨⟨by word, by word⟩, rfl⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.Z j < sint.Z (nv.inodes'.len - W64 2) := Hif
    have Hlt' : sint.Z j < sint.Z nv.inodes'.len - 2 := by word
    list_elem ins (sint.nat j) as it
    have HitL : (ins.take (ins.length - 2))[sint.nat j]? = some it := by
      rw [List.getElem?_take_of_lt (by word)]; exact Hit_lookup
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hj.1, by word⟩)]
    wp_apply wp_load_slice_index _ (sint.Z j) ins dqs it Hj.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hit_lookup
    try wp_auto
    wp_apply hPE $$ [$Hn] as Hn
    try wp_auto
    wp_apply hK $$ [$inode] as inode
    try wp_auto
    wp_apply hV $$ [$inode] as inode
    try wp_auto
    rw [splitIndexGo_drop _ _ _ _ _ _ HitL] at Hr
    have Hjw : W64 ((sint.nat j : Nat) : Int) = j := by word
    rw [Hjw] at Hr
    wp_if_destruct
    · wp_if_destruct
      · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)] at Hr
        wp_for_post
        rw [Hr]
        iapply HΦ; iframe
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (by intro h; obtain ⟨h1, h2⟩ := h; word))] at Hr
        wp_for_post
        iframe
        iexists j + W64 1, j, _
        iframe
        have Hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
        rw [Hj1]
        ipureintro; exact ⟨⟨by word, fun _ => by word⟩, Hr⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by intro h; obtain ⟨h1, h2⟩ := h; word))] at Hr
      wp_for_post
      iframe
      iexists j + W64 1, j, _
      iframe
      have Hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      rw [Hj1]
      ipureintro; exact ⟨⟨by word, fun _ => by word⟩, Hr⟩
  · have Hge : sint.Z (nv.inodes'.len - W64 2) ≤ sint.Z j := by have := Hif; word
    have Heq : (ins.take (ins.length - 2)).drop (sint.nat j) = [] := by
      apply List.drop_of_length_le; simp only [List.length_take]; rw [Hsl.1]; word
    rw [Heq, show splitIndexGo thr (sint.nat j) idx sz [] = (idx, sz) from rfl] at Hr
    try wp_auto
    rw [Hr]
    iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
