/-
`Bucket.write` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U9b; used by U7 (`CreateBucket*`'s new bucket), U9b (`Bucket.spill`). Proof:
`Proof/go_etcd_io/bbolt/Bucket__write.lean` (a `sorry` until U9b).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `b.write()` of a bucket whose root node is a leaf with the inodes `ms` (their bytes read at
`dqk`; a fresh bucket's empty leaf, or an inlineable child's): a new byte slice, its header
`b.InBucket`'s and then the root node written as an inline page (header id `0`, a leaf of
`ms.length` elements, `pageBody`), sized by `node.size`. -/
abbrev Bucket.write.spec : Prop :=
  ∀ (b ibp : Loc) (ib : InBucket) (n : Loc) (nv : node) (ins : List Inode) (ms : List InodeM)
    (dqb dq dqi : DFrac) (qk qv : Nat → DFrac),
  nv.isLeaf' = true → ms.length < 0xFFFF → pageFits ms →
  insSize ins = 16 + (pageBody true ms).length → insSize ins < 2 ^ 31 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      b.[Bucket, go!"InBucket"] ↦{dqb} ibp ∗ ibp ↦{dqb} ib ∗ b.[Bucket, go!"rootNode"] ↦{dqb} n ∗
      n ↦{dq} nv ∗ nv.inodes' ↦*{dqi} ins ∗
      ([∗list] k ↦ it;m ∈ ins;ms, ⌜it.flags' = m.flags ∧ it.pgid' = m.pgid⌝ ∗
        it.key' ↦*{qk k} m.key ∗ it.value' ↦*{qv k} m.value) }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"write")) (Val #()))
  {{ (value : GoSlice), RET #value;
      value ↦* (encode ib ++ encode (hdrWritten ⟨W64 0, W16 0, W16 0, W32 0⟩ true ms.length) ++
        pageBody true ms) ∗ ownSliceCap w8 value (DFrac.own 1) ∗
      b.[Bucket, go!"InBucket"] ↦{dqb} ibp ∗ ibp ↦{dqb} ib ∗ b.[Bucket, go!"rootNode"] ↦{dqb} n ∗
      n ↦{dq} nv ∗ nv.inodes' ↦*{dqi} ins ∗
      ([∗list] k ↦ it;m ∈ ins;ms, ⌜it.flags' = m.flags ∧ it.pgid' = m.pgid⌝ ∗
        it.key' ↦*{qk k} m.key ∗ it.value' ↦*{qv k} m.value) }}

end spec

end bbolt
end EtcdGrove
end Perennial
