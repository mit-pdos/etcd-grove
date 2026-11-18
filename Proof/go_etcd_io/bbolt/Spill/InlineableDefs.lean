/-
`inlineIns`, its size lemmas and the specs of `Bucket.maxInlineBucketSize` and `Bucket.inlineable`,
out of `Inlineable.lean`'s proofs so that the spill modules import them without the proofs (import
tiers, 2026-11-18).
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

open Fs

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
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
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
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

end proof

end bbolt
end EtcdGrove
end Perennial
