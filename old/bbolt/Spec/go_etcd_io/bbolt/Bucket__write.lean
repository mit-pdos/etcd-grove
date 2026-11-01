module
public import Proof.go_etcd_io.bbolt.NodeModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section defs
variable [ext : FfiSyntax]

/-- The page header `n.write` leaves on a zeroed page: id 0, the node's kind, its count. -/
def writtenHdr (leaf : Bool) (n : Nat) : Page :=
  Page.mk (W64 0) (if leaf then W16 2 else W16 1) (W16 (n : Int)) (W32 0)

/-- The value `b.write()` returns: the bucket's header, then its root node written as a page. -/
def writtenBucket (ib : InBucket) (leaf : Bool) (ks vs : List (List w8)) (ins : List Inode) :
    List w8 :=
  inBucketBytes ib ++ pageBytes (writtenHdr leaf ins.length) ++ writtenElems leaf ks vs ins ++
    kvBytes ks vs

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `b.write()`: the bucket's header and its root node (keys `ks`, values `vs`) as an inline
bucket's value, in a new slice. -/
abbrev Bucket.write.spec : Prop :=
  ∀ (bl : Loc) (bv : Bucket) (dqb : DFrac) (ib : InBucket) (dqi : DFrac) (nv : node) (dqn : DFrac)
    (ins : List Inode) (dqs : DFrac) (ks vs : List (List w8)) (q : DFrac),
  ins.length < 65535 → ks.length = ins.length → vs.length = ins.length →
  (∀ i < ins.length, 0 < (ks.getD i []).length) →
  16 + 16 * ins.length + kvLen ks vs ins.length ≤ 2147483647 →
  sizeFrom (W64 16) (W64 16) ins = W64 ((16 + 16 * ins.length + kvLen ks vs ins.length : Nat) : Int) →
  (nv.isLeaf' = false → ∀ i < ins.length, (ins.getD i (zero_val Inode)).pgid' ≠ W64 0) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ bl ↦{dqb} bv ∗ bv.InBucket' ↦{dqi} ib ∗
      bv.rootNode' ↦{dqn} nv ∗ nv.inodes' ↦*{dqs} ins ∗ inodeData ins ks vs q }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"write")) (Val #()))
  {{ (val : GoSlice), RET #val; bl ↦{dqb} bv ∗ bv.InBucket' ↦{dqi} ib ∗
      bv.rootNode' ↦{dqn} nv ∗ nv.inodes' ↦*{dqs} ins ∗ inodeData ins ks vs q ∗
      val ↦* writtenBucket ib nv.isLeaf' ks vs ins ∗ ownSliceCap w8 val (DFrac.own 1) }}

end spec

end bbolt
end EtcdGrove
end Perennial
