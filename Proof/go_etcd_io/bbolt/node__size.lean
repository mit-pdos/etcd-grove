module
public import Spec.go_etcd_io.bbolt.node__size
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

theorem node.size.wp_proof (hPE : node.pageElementSize.spec (GF := GF) (hG := hG))
    (hK : Inode.Key.spec (GF := GF) (hG := hG))
    (hV : Inode.Value.spec (GF := GF) (hG := hG)) :
    node.size.spec (GF := GF) (hG := hG) := by
  intro nl nv dq ins dqs
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
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z nv.inodes'.len⌝ : IProp GF) $$ [i sz Hs Hn]
  · iexists W64 0
    simp only [named]
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.Z j < sint.Z nv.inodes'.len := Hif
    have Hjn : sint.nat j < ins.length := by rw [Hsl.1]; word
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hj.1, Hlt⟩)]
    icases ownSlice_elem_acc (sint.Z j) (ins[sint.nat j]'Hjn) _ _ ins Hj.1
      (List.getElem?_eq_getElem Hjn) $$ Hs with ⟨Hit, Hsback⟩
    try wp_auto
    wp_apply hK $$ [$Hit] as Hit
    try wp_auto
    wp_apply hV $$ [$Hit] as Hit
    try wp_auto
    ihave Hs := Hsback $$ Hit
    rw [List.set_getElem_self]
    wp_for_post
    iframe
    iexists j + W64 1
    iframe
    isplitl
    · rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_succ,
        List.getElem?_eq_getElem Hjn]
      simp only [Option.toList_some]
      rw [sizeFrom_append]
      iExactEq sz
      congr 2
    · ipureintro; constructor <;> word
  · have Heq : sint.nat j = ins.length := by rw [Hsl.1]; word
    try wp_auto
    rw [Heq, List.take_length]
    iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
