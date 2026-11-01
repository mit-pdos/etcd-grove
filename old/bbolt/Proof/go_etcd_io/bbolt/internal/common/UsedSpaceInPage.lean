module
public import Spec.go_etcd_io.bbolt.internal.common.UsedSpaceInPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__PageElementSize
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Value

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

theorem UsedSpaceInPage.wp_proof (hPE : Page.PageElementSize.spec (GF := GF) (hG := hG))
    (hK : Inode.Key.spec (GF := GF) (hG := hG)) (hV : Inode.Value.spec (GF := GF) (hG := hG)) :
    UsedSpaceInPage.spec (GF := GF) (hG := hG) := by
  intro s ins dq p v dq'
  wp_start as ⟨Hs, Hp⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  wp_auto
  wp_apply hPE $$ [$Hp] as Hp
  try wp_auto
  ihave IH : (∃ (j : w64),
      "i" ∷ i_ptr ↦ j ∗ "off" ∷ off_ptr ↦ usedSpaceFrom (W64 16 + W64 16 * s.len) (ins.take (sint.nat j)) ∗
      "Hs" ∷ s ↦*{dq} ins ∗ "Hp" ∷ p ↦{dq'} v ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.len⌝ : IProp GF) $$ [i off Hs Hp]
  · iexists W64 0
    simp only [named]
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.Z j < sint.Z s.len := Hif
    have Hjn : sint.nat j < ins.length := by rw [Hsl.1]; word
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hj.1, Hlt⟩)]
    wp_apply wp_load_slice_index s (sint.Z j) ins dq (ins[sint.nat j]'Hjn) Hj.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact List.getElem?_eq_getElem Hjn
    try wp_auto
    wp_apply hK $$ [$item] as item
    try wp_auto
    wp_apply hV $$ [$item] as item
    try wp_auto
    wp_for_post
    iframe
    iexists j + W64 1
    iframe
    isplitl
    · rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_succ,
        List.getElem?_eq_getElem Hjn]
      unfold usedSpaceFrom
      rw [List.foldl_append]
      simp only [Option.toList_some, List.foldl_cons, List.foldl_nil]
      iExactEq off
      congr 2
    · ipureintro; constructor <;> word
  · have Hge : sint.Z s.len ≤ sint.Z j := by have := Hif; word
    have Heq : sint.nat j = ins.length := by rw [Hsl.1]; word
    try wp_auto
    rw [Heq, List.take_length]
    iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
