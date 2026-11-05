/-
`Bucket.inlineable` and `Bucket.maxInlineBucketSize` (U9c, `notes/bbolt-proof-plan.md`;
unit-internal, stated and proved here; ported from `old/bbolt/.../Bucket__inlineable.lean`).

`b.inlineable()` is true iff the bucket's root node is materialized, a leaf, with no nested bucket
among its inodes, and the page they make (`insSize`) within a quarter page (`pageSize / 4 = 1024`,
`dbFixed`'s page size). Its sizes are `uintptr` sums, cut off at the first inode past the limit;
the premise bounds the non-bucket inodes' key and value lengths so that no sum wraps (a bucket
inode's value is never added up to a decision). Stated over the points-tos it reads, as
`Bucket.write`'s, for `Bucket.spill`'s child buckets.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Value
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Flags

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- **Inodes that fit inline**: none a nested bucket, and their page (`insSize`) within
`maxInlineBucketSize` (a quarter of the 4096-byte page). -/
def inlineIns (ins : List Inode) : Prop :=
  (∀ it ∈ ins, it.flags' &&& W32 1 = W32 0) ∧ insSize ins ≤ 1024

instance (ins : List Inode) : Decidable (inlineIns ins) := by unfold inlineIns; infer_instance

theorem insSize_snoc' (ins : List Inode) (it : Inode) :
    insSize (ins ++ [it]) = insSize ins + (16 + it.key'.len.toNat + it.value'.len.toNat) := by
  simp only [insSize, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]; omega

private theorem insSize_take_le (ins : List Inode) (k : Nat) : insSize (ins.take k) ≤ insSize ins := by
  conv => rhs; rw [← List.take_append_drop k ins]
  simp only [insSize, List.map_append, List.sum_append]; omega

theorem insSize_snoc_lt (a : List Inode) (it : Inode) (h1 : insSize a ≤ 1024)
    (h2 : it.key'.len.toNat + it.value'.len.toNat < 2 ^ 62) : insSize (a ++ [it]) < 2 ^ 63 := by
  rw [insSize_snoc']; omega

theorem insSize_snoc_w64 (a : List Inode) (it : Inode) :
    W64 ↑(insSize a) + (W64 16 + it.key'.len + it.value'.len) = W64 ↑(insSize (a ++ [it])) := by
  rw [insSize_snoc']; word

end pure

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`b.maxInlineBucketSize()`**: a quarter of the database's page size. -/
abbrev Bucket.maxInlineBucketSize.spec : Prop :=
  ∀ (b tx db : Loc) (dqt dqd : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ b.[Bucket, go!"tx"] ↦{dqt} tx ∗
      tx.[Tx, go!"db"] ↦{dqd} db ∗ db.[DB, go!"pageSize"] ↦□ W64 4096 }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"maxInlineBucketSize")) (Val #()))
  {{ RET #(W64 1024); b.[Bucket, go!"tx"] ↦{dqt} tx ∗ tx.[Tx, go!"db"] ↦{dqd} db }}

/-- **`b.inlineable()`** of a bucket whose root node is `n` (its struct `nv` and inodes `ins`
when it is not nil): whether `n` is a leaf whose inodes fit inline (`inlineIns`). -/
abbrev Bucket.inlineable.spec : Prop :=
  ∀ (b n : Loc) (nv : node) (ins : List Inode) (tx db : Loc) (dqb dq dqi dqt dqd : DFrac),
  (∀ it ∈ ins, it.flags' &&& W32 1 = W32 0 → it.key'.len.toNat + it.value'.len.toNat < 2 ^ 62) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ b.[Bucket, go!"rootNode"] ↦{dqb} n ∗
      (if n = null then emp else n ↦{dq} nv ∗ nv.inodes' ↦*{dqi} ins) ∗
      b.[Bucket, go!"tx"] ↦{dqt} tx ∗ tx.[Tx, go!"db"] ↦{dqd} db ∗
      db.[DB, go!"pageSize"] ↦□ W64 4096 }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"inlineable")) (Val #()))
  {{ RET #(decide (n ≠ null ∧ nv.isLeaf' = true ∧ inlineIns ins));
      b.[Bucket, go!"rootNode"] ↦{dqb} n ∗
      (if n = null then emp else n ↦{dq} nv ∗ nv.inodes' ↦*{dqi} ins) ∗
      b.[Bucket, go!"tx"] ↦{dqt} tx ∗ tx.[Tx, go!"db"] ↦{dqd} db }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Bucket.maxInlineBucketSize.wp_proof : Bucket.maxInlineBucketSize.spec (GF := GF) (hG := hG) := by
  intro b tx db dqt dqd
  wp_start as ⟨Hb, Hdb, #Hps⟩
  wp_auto
  rw [show BitVec.sdiv (W64 4096) (W64 4) = W64 1024 by rfl]
  iapply HΦ
  iframe

theorem Bucket.inlineable.wp_proof (hK : internal.common.Inode.Key.spec (GF := GF) (hG := hG))
    (hV : internal.common.Inode.Value.spec (GF := GF) (hG := hG))
    (hF : internal.common.Inode.Flags.spec (GF := GF) (hG := hG)) :
    Bucket.inlineable.spec (GF := GF) (hG := hG) := by
  intro b n nv ins tx db dqb dq dqi dqt dqd hbnd
  wp_start as ⟨Hrn, Hn, Htx, Hdb, #Hps⟩
  wp_auto
  by_cases hnull : n = null
  · subst hnull
    wp_auto
    simp only [ne_eq, not_true_eq_false, false_and, decide_false]
    iapply HΦ
    iframe
  · isimp only [hnull, ↓reduceIte] at Hn
    icases Hn with ⟨Hn, Hins⟩
    ihave %Hsl := ownSlice_len _ _ _ $$ Hins
    iStructNamed Hn
    rw [decide_eq_false hnull]
    wp_auto
    cases hleaf : nv.isLeaf'
    · wp_auto
      ihave Hn : (n ↦{dq} nv : IProp GF) $$
          [bucket isLeaf unbalanced spilled key pgid parent children inodes]
      · iapply typedPointsto_combine _ _ _ hnull
        simp only [TypedPointsto.typedPointstoDef, hleaf]
        iframe
      simp only [Bool.false_eq_true, false_and, and_false, decide_false]
      iapply HΦ
      rw [ite_eq_right_of_eq_false _ _ (eq_false hnull)]
      iframe
    · unfold internal.common.PageHeaderSize internal.common.LeafPageElementSize
      wp_auto
      ihave IH : (∃ (j : w64),
          "i" ∷ i_ptr ↦ j ∗ "size" ∷ size_ptr ↦ W64 (insSize (ins.take (sint.nat j)) : Int) ∗
          "Hins" ∷ nv.inodes' ↦*{dqi} ins ∗ "b" ∷ b_ptr ↦ b ∗ "Htx" ∷ b.[Bucket, go!"tx"] ↦{dqt} tx ∗
          "Hdb" ∷ tx.[Tx, go!"db"] ↦{dqd} db ∗ "Hres" ∷ «$res0_ptr» ↦ zero_val Bool ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z nv.inodes'.len ∧
            inlineIns (ins.take (sint.nat j))⌝ : IProp GF) $$ [i size Hins b Htx Hdb «$res0»]
      · iexists W64 0
        simp only [named]
        rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
        iframe
        ipureintro
        refine ⟨by word, by word, ?_, ?_⟩
        · intro it h; simp at h
        · simp [insSize]
      irename : ("_" ∷ True : IProp GF) => Htriv
      iclear Htriv
      wp_for IH
      wp_if_destruct
      · have Hlt : sint.nat j < ins.length := by rw [Hsl.1]; word
        have Hbnd : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z nv.inodes'.len := ⟨Hj.1, Hif⟩
        simp only [Hbnd, and_self, ↓reduceIte]
        obtain ⟨it, Hit⟩ : ∃ it, ins[sint.nat j]? = some it := ⟨_, List.getElem?_eq_getElem Hlt⟩
        wp_apply wp_load_slice_index nv.inodes' (sint.Z j) _ dqi it Hj.1 $$ [Hins] as Hins
        · iframe; ipureintro; exact Hit
        try wp_auto
        wp_apply hK $$ [$inode] as inode
        try wp_auto
        wp_apply hV $$ [$inode] as inode
        try wp_auto
        wp_apply hF $$ [$inode] as inode
        try wp_auto
        have Hmem : it ∈ ins := List.mem_of_getElem? Hit
        have Htake : ins.take (sint.nat j + 1) = ins.take (sint.nat j) ++ [it] := by
          rw [List.take_add_one, Hit]; rfl
        by_cases hf : it.flags' &&& W32 1 = W32 0
        · rw [decide_eq_true hf]
          wp_auto
          wp_apply Bucket.maxInlineBucketSize.wp_proof $$ [$Htx $Hdb] as ⟨Htx, Hdb⟩
          · iexact Hps
          have hkv := hbnd it Hmem hf
          have hS0 := Hj.2.2.2
          have Hsz : W64 ↑(insSize (List.take (sint.nat j) ins)) + (W64 16 + it.key'.len + it.value'.len) =
              W64 ↑(insSize (ins.take (sint.nat j + 1))) := by
            rw [Htake]; exact insSize_snoc_w64 _ _
          rw [Hsz]
          have hS : insSize (ins.take (sint.nat j + 1)) < 2 ^ 63 := by
            rw [Htake]; exact insSize_snoc_lt _ _ hS0 hkv
          by_cases hle : insSize (ins.take (sint.nat j + 1)) ≤ 1024
          · have hgt : ¬ (uint.Z (W64 1024) < uint.Z (W64 ↑(insSize (ins.take (sint.nat j + 1))))) := by
              word
            rw [decide_eq_false hgt]
            wp_auto
            wp_for_post
            iframe
            iexists j + W64 1
            rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word]
            iframe
            ipureintro
            refine ⟨by word, by word, ?_, hle⟩
            intro x hx
            rw [Htake] at hx
            rcases List.mem_append.1 hx with hx | hx
            · exact Hj.2.2.1 x hx
            · rw [List.mem_singleton.1 hx]; exact hf
          · have hgt : uint.Z (W64 1024) < uint.Z (W64 ↑(insSize (ins.take (sint.nat j + 1)))) := by
              word
            rw [decide_eq_true hgt]
            wp_auto
            wp_for_post
            have hno : ¬ inlineIns ins := fun h => hle (Nat.le_trans (insSize_take_le _ _) h.2)
            simp only [hno, _root_.and_false, decide_false]
            ihave Hn : (n ↦{dq} nv : IProp GF) $$
                [bucket isLeaf unbalanced spilled key pgid parent children inodes]
            · iapply typedPointsto_combine _ _ _ hnull
              simp only [TypedPointsto.typedPointstoDef, hleaf]
              iframe
            iapply HΦ
            rw [ite_eq_right_of_eq_false _ _ (eq_false hnull)]
            iframe
        · rw [decide_eq_false hf]
          wp_auto
          wp_for_post
          have hno : ¬ inlineIns ins := fun h => hf (h.1 it Hmem)
          simp only [hno, _root_.and_false, decide_false]
          ihave Hn : (n ↦{dq} nv : IProp GF) $$
              [bucket isLeaf unbalanced spilled key pgid parent children inodes]
          · iapply typedPointsto_combine _ _ _ hnull
            simp only [TypedPointsto.typedPointstoDef, hleaf]
            iframe
          iapply HΦ
          rw [ite_eq_right_of_eq_false _ _ (eq_false hnull)]
          iframe
      · have Heq : sint.nat j = ins.length := by rw [Hsl.1]; word
        rw [Heq, List.take_length] at Hj
        try wp_auto
        simp only [ne_eq, hnull, not_false_eq_true, _root_.true_and, Hj.2.2, _root_.decide_true]
        ihave Hn : (n ↦{dq} nv : IProp GF) $$
            [bucket isLeaf unbalanced spilled key pgid parent children inodes]
        · iapply typedPointsto_combine _ _ _ hnull
          simp only [TypedPointsto.typedPointstoDef, hleaf]
          iframe
        iapply HΦ
        try rw [ite_eq_right_of_eq_false _ _ (eq_false hnull)]
        simp only [if_false]
        iframe

end proof

end bbolt
end EtcdGrove
end Perennial
