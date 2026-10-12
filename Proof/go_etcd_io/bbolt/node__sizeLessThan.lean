module
public import Spec.go_etcd_io.bbolt.node__sizeLessThan
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

theorem node.sizeLessThan.wp_proof (hPE : node.pageElementSize.spec (GF := GF) (hG := hG))
    (hK : Inode.Key.spec (GF := GF) (hG := hG))
    (hV : Inode.Value.spec (GF := GF) (hG := hG)) :
    node.sizeLessThan.spec (GF := GF) (hG := hG) := by
  intro nl nv dq ins dqs v
  wp_start as ⟨Hn, Hs⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  wp_auto
  wp_apply hPE $$ [$Hn] as Hn
  try wp_auto
  unfold internal.common.PageHeaderSize
  wp_auto
  ihave IH : (∃ (j : w64),
      "i" ∷ i_ptr ↦ j ∗ "sz" ∷ sz_ptr ↦ sizeFrom (W64 16) (W64 16) (ins.take (sint.nat j)) ∗
      "Hs" ∷ nv.inodes' ↦*{dqs} ins ∗ "Hn" ∷ nl ↦{dq} nv ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z nv.inodes'.len⌝ ∗
      "%Hr" ∷ ⌜sizeLessThanFrom (W64 16) v (W64 16) ins =
        sizeLessThanFrom (W64 16) v (sizeFrom (W64 16) (W64 16) (ins.take (sint.nat j)))
          (ins.drop (sint.nat j))⌝ : IProp GF) $$ [i sz Hs Hn]
  · iexists W64 0
    simp only [named]
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero]
    iframe
    ipureintro; refine ⟨⟨by word, by word⟩, rfl⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.Z j < sint.Z nv.inodes'.len := Hif
    list_elem ins (sint.nat j) as it
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hj.1, Hlt⟩)]
    icases ownSlice_elem_acc (sint.Z j) it _ _ ins Hj.1 Hit_lookup $$ Hs with ⟨Hit, Hsback⟩
    try wp_auto
    wp_apply hK $$ [$Hit] as Hit
    try wp_auto
    wp_apply hV $$ [$Hit] as Hit
    try wp_auto
    ihave Hs := Hsback $$ Hit
    rw [list_set_lookup_self _ _ _ Hit_lookup]
    rw [sizeLessThanFrom_drop _ _ _ _ _ _ Hit_lookup] at Hr
    wp_if_destruct
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))] at Hr
      wp_for_post
      rw [Hr]
      iapply HΦ; iframe
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by word))] at Hr
      wp_for_post
      iframe
      iexists j + W64 1
      iframe
      have Hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      rw [Hj1, take_succ_of_get _ _ _ Hit_lookup, sizeFrom_append]
      isplitl
      · iExactEq sz
        congr 2
      · ipureintro; exact ⟨⟨by word, by word⟩, Hr⟩
  · have Heq : sint.nat j = ins.length := by rw [Hsl.1]; word
    try wp_auto
    rw [Heq, List.drop_length, sizeLessThanFrom_nil] at Hr
    rw [Hr]
    iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
