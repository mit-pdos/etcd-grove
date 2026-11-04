/-
`node.pageElementSize`, `node.sizeLessThan` and `node.splitIndex` (U9a, `notes/bbolt-proof-plan.md`):
unit-internal functions of the spill, stated and proved here over the node's points-to and its
inodes slice (only the slices' headers are read), with `Spill/SplitModel`'s model.
-/
module

public import Spec.go_etcd_io.bbolt.node__size
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Value
public import Proof.go_etcd_io.bbolt.Spill.SplitModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `n.pageElementSize()`: 16, for a leaf as for a branch. -/
abbrev node.pageElementSize.spec : Prop :=
  ∀ (n : Loc) (nv : node) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ n ↦{dq} nv }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"pageElementSize")) (Val #()))
  {{ RET #(W64 16); n ↦{dq} nv }}

/-- `n.sizeLessThan(v)`: whether the node is empty or its page (`insSize`) is below `v`. -/
abbrev node.sizeLessThan.spec : Prop :=
  ∀ (n : Loc) (nv : node) (ins : List Inode) (dq dqi : DFrac) (v : w64),
  insSize ins < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ n ↦{dq} nv ∗ nv.inodes' ↦*{dqi} ins }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"sizeLessThan")) (Val #v))
  {{ RET #(decide (ins = [] ∨ insSize ins < v.toNat)); n ↦{dq} nv ∗ nv.inodes' ↦*{dqi} ins }}

/-- `n.splitIndex(t)` with a non-negative threshold: `splitIdx`'s index and size. -/
abbrev node.splitIndex.spec : Prop :=
  ∀ (n : Loc) (nv : node) (ins : List Inode) (dq dqi : DFrac) (t : w64),
  insSize ins < 2 ^ 63 → 0 ≤ sint.Z t →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ n ↦{dq} nv ∗ nv.inodes' ↦*{dqi} ins }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"splitIndex")) (Val #t))
  {{ RET (PairV #(W64 ((splitIdx (sint.nat t) ins).1 : Int)) #(W64 ((splitIdx (sint.nat t) ins).2 : Int)));
      n ↦{dq} nv ∗ nv.inodes' ↦*{dqi} ins }}

end spec

theorem uintZ_W64_nat (x : Nat) (h : x < 2 ^ 64) : uint.Z (W64 (x : Int)) = (x : Int) := by
  word

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem node.pageElementSize.wp_proof : node.pageElementSize.spec (GF := GF) (hG := hG) := by
  intro nl nv dq
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

theorem node.sizeLessThan.wp_proof (hK : internal.common.Inode.Key.spec (GF := GF) (hG := hG))
    (hV : internal.common.Inode.Value.spec (GF := GF) (hG := hG)) :
    node.sizeLessThan.spec (GF := GF) (hG := hG) := by
  intro nl nv ins dq dqs v Hbnd
  wp_start as ⟨Hn, Hs⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
  wp_auto
  wp_apply node.pageElementSize.wp_proof $$ [$Hn] as Hn
  try wp_auto
  unfold internal.common.PageHeaderSize
  wp_auto
  ihave IH : (∃ (j : w64),
      "i" ∷ i_ptr ↦ j ∗ "sz" ∷ sz_ptr ↦ W64 (insSize (ins.take (sint.nat j)) : Int) ∗
      "Hs" ∷ nv.inodes' ↦*{dqs} ins ∗ "Hn" ∷ nl ↦{dq} nv ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z nv.inodes'.len ∧
        (0 < sint.nat j → insSize (ins.take (sint.nat j)) < v.toNat)⌝ : IProp GF) $$ [i sz Hs Hn]
  · iexists W64 0
    simp only [named]
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    iframe
    ipureintro; refine ⟨by word, by word, fun h => absurd h (by decide)⟩
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
    have Htk : ins.take (sint.nat j + 1) = ins.take (sint.nat j) ++ [it] := by
      rw [List.take_add_one, show sint.nat j = (sint.Z j).toNat from rfl, Hit_lookup]; rfl
    have Hnext : insSize (ins.take (sint.nat j + 1)) = insSize (ins.take (sint.nat j)) + inSz it := by
      rw [Htk, insSize_snoc]
    have Hle : insSize (ins.take (sint.nat j + 1)) ≤ insSize ins := insSize_take_le _ _
    have Hsz : W64 (insSize (ins.take (sint.nat j)) : Int) + (W64 16 + it.key'.len + it.value'.len) =
        W64 (insSize (ins.take (sint.nat j + 1)) : Int) := by
      rw [Hnext]; unfold inSz; word
    rw [Hsz]
    have H64 : insSize (ins.take (sint.nat j + 1)) < 2 ^ 64 := by omega
    wp_if_destruct
    · have Hge : v.toNat ≤ insSize (ins.take (sint.nat j + 1)) := by
        rw [uintZ_W64_nat _ H64] at Hif; unfold uint.Z at Hif; omega
      have Hres : decide (ins = [] ∨ insSize ins < v.toNat) = false := by
        have : ins ≠ [] := by intro h; subst h; simp at Hjn
        simp only [decide_eq_false_iff_not, not_or]; exact ⟨this, by omega⟩
      wp_for_post
      try wp_auto
      rw [Hres]
      iapply HΦ; iframe
    · wp_for_post
      iframe
      iexists j + W64 1
      iframe
      have Hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      rw [Hj1]
      iframe
      ipureintro
      refine ⟨by word, by word, fun _ => ?_⟩
      rw [uintZ_W64_nat _ H64] at Hif; unfold uint.Z at Hif; omega
  · have Hge : ¬ sint.Z j < sint.Z nv.inodes'.len := by
      intro h; simp [h] at Hif
    simp only [Hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    have Heq : sint.nat j = ins.length := by rw [Hsl.1]; word
    try wp_auto
    rw [Heq, List.take_length] at Hj
    have Hres : decide (ins = [] ∨ insSize ins < v.toNat) = true := by
      rcases Nat.eq_zero_or_pos ins.length with h | h
      · simp [List.eq_nil_of_length_eq_zero h]
      · simp only [decide_eq_true_eq]; exact Or.inr (Hj.2.2 h)
    rw [Hres]
    iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
