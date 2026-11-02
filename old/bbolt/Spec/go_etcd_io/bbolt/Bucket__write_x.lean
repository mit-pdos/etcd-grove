module
public import Spec.go_etcd_io.bbolt.Bucket__write
public import Spec.go_etcd_io.bbolt.node__write_x

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `b.write()` (`Bucket.write.spec`), the inodes' keys and values at fractions of their own: the bucket's header and its root node (keys `ks`, values `vs`) as an inline
bucket's value, in a new slice. -/
abbrev Bucket.write.xspec : Prop :=
  ∀ (bl : Loc) (bv : Bucket) (dqb : DFrac) (ib : InBucket) (dqi : DFrac) (nv : node) (dqn : DFrac)
    (ins : List Inode) (dqs : DFrac) (ks vs : List (List w8)) (qk qv : Nat → DFrac),
  ins.length < 65535 → ks.length = ins.length → vs.length = ins.length →
  (∀ i < ins.length, 0 < (ks.getD i []).length) →
  16 + 16 * ins.length + kvLen ks vs ins.length ≤ 2147483647 →
  sizeFrom (W64 16) (W64 16) ins = W64 ((16 + 16 * ins.length + kvLen ks vs ins.length : Nat) : Int) →
  (nv.isLeaf' = false → ∀ i < ins.length, (ins.getD i (zero_val Inode)).pgid' ≠ W64 0) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ bl ↦{dqb} bv ∗ bv.InBucket' ↦{dqi} ib ∗
      bv.rootNode' ↦{dqn} nv ∗ nv.inodes' ↦*{dqs} ins ∗ inodeDataF ins ks vs qk qv }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"write")) (Val #()))
  {{ (val : GoSlice), RET #val; bl ↦{dqb} bv ∗ bv.InBucket' ↦{dqi} ib ∗
      bv.rootNode' ↦{dqn} nv ∗ nv.inodes' ↦*{dqs} ins ∗ inodeDataF ins ks vs qk qv ∗
      val ↦* writtenBucket ib nv.isLeaf' ks vs ins ∗ ownSliceCap w8 val (DFrac.own 1) }}

end spec

end bbolt
end EtcdGrove
end Perennial
