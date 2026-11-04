/-
The proof of `Spec/go_etcd_io/bbolt/node__size.lean` (U9a, `notes/bbolt-proof-plan.md`; ported from
`old/bbolt/Proof/go_etcd_io/bbolt/node__size.lean`). `node.pageElementSize` (16 for either kind) is
proved inline: it is unit-internal.
-/
module

public import Spec.go_etcd_io.bbolt.node__size
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Value

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

private theorem insSize_snoc (ins : List Inode) (it : Inode) :
    insSize (ins ++ [it]) = insSize ins + (16 + it.key'.len.toNat + it.value'.len.toNat) := by
  simp only [insSize, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]; omega

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

omit hos in
private theorem node.pageElementSize.wp_spec (nl : Loc) (nv : node) (dq : DFrac) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ nl ↦{dq} nv }}
    (App (Val (nl @!! go.GoType.PointerType node.ty @!! go!"pageElementSize")) (Val #()))
  {{ RET #(W64 16); nl ↦{dq} nv }} := by
  wp_start as Hn
  unfold internal.common.BranchPageElementSize internal.common.LeafPageElementSize
  icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
  iStructNamed Hn
  wp_auto
  ihave Hn : (nl ↦{dq} nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  cases h : nv.isLeaf' <;> (try simp only [Bool.false_eq_true, ↓reduceIte]) <;> wp_auto <;>
    iapply HΦ <;> iframe

omit hos in
theorem node.size.wp_proof (hK : internal.common.Inode.Key.spec (GF := GF) (hG := hG))
    (hV : internal.common.Inode.Value.spec (GF := GF) (hG := hG)) :
    node.size.spec (GF := GF) (hG := hG) := by
  intro nl nv ins dq dqs
  wp_start as ⟨Hn, Hs⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
  wp_auto
  wp_apply node.pageElementSize.wp_spec $$ [$Hn] as Hn
  try wp_auto
  unfold internal.common.PageHeaderSize
  wp_auto
  ihave IH : (∃ (j : w64),
      "i" ∷ i_ptr ↦ j ∗ "sz" ∷ sz_ptr ↦ W64 (insSize (ins.take (sint.nat j)) : Int) ∗
      "Hs" ∷ nv.inodes' ↦*{dqs} ins ∗ "Hn" ∷ nl ↦{dq} nv ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z nv.inodes'.len⌝ : IProp GF) $$ [i sz Hs Hn]
  · iexists W64 0
    simp only [named]
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  iStructNamed Hn
  wp_auto
  ihave Hn : (nl ↦{dq} nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  wp_if_destruct
  · have Hlt : sint.Z j < sint.Z nv.inodes'.len := by
      refine Classical.byContradiction fun h => ?_; simp [h, false_neq_true] at Hif
    have Hjn : sint.nat j < ins.length := by rw [Hsl.1]; word
    iStructNamed Hn
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hj.1, Hlt⟩)]
    list_elem ins (sint.Z j).toNat as it
    icases ownSlice_elem_acc (sint.Z j) it _ _ ins Hj.1 Hit_lookup $$ Hs with ⟨Hit, Hsback⟩
    try wp_auto
    ihave Hn : (nl ↦{dq} nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    wp_apply hK $$ [$Hit] as Hit
    try wp_auto
    wp_apply hV $$ [$Hit] as Hit
    try wp_auto
    ihave Hs := Hsback $$ Hit
    rw [list_set_lookup_self _ _ _ Hit_lookup]
    wp_for_post
    iframe
    iexists j + W64 1
    iframe
    isplitl
    · rw [show sint.nat (j + W64 1) = (sint.Z j).toNat + 1 by word, List.take_add_one, Hit_lookup,
        show sint.nat j = (sint.Z j).toNat from rfl]
      simp only [Option.toList_some]
      rw [insSize_snoc]
      iExactEq sz
      congr 1
      word
    · ipureintro; constructor <;> word
  · have Hge : ¬ sint.Z j < sint.Z nv.inodes'.len := by
      intro h; simp [h] at Hif
    simp only [Hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    have Heq : sint.nat j = ins.length := by rw [Hsl.1]; word
    try wp_auto
    rw [Heq, List.take_length]
    iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
