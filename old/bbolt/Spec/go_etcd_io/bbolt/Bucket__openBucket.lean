module
public import Proof.go_etcd_io.bbolt.BucketOpen

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `b.openBucket(value)` in a read transaction: a new bucket (`openedBucketOf`) whose header
is the value's first 16 bytes, read in place (`ibl = value.ptr`) or, when the value is not
8-aligned (`ptrAddr`), in a copy `c` of it, owned by the caller; for an inline bucket (root 0)
its page is the rest. The value must hold a header (and, for an inline bucket, more: `openBucket`
takes `&value[16]`, which panics otherwise). -/
abbrev Bucket.openBucket.spec : Prop :=
  ∀ (bl : Loc) (bv : Bucket) (dqb dqw : DFrac) (value : GoSlice) (v : List w8) (dv : DFrac),
  16 ≤ v.length → (inBucketRoot v = 0 → 16 < v.length) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ bl ↦{dqb} bv ∗
      structFieldRef Tx go!"writable" bv.tx' ↦{dqw} false ∗ value ↦*{dv} v }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"openBucket")) (Val #value))
  {{ (cl ibl : Loc), RET #cl; bl ↦{dqb} bv ∗ structFieldRef Tx go!"writable" bv.tx' ↦{dqw} false ∗
      value ↦*{dv} v ∗ cl ↦ openedBucketOf bv.tx' ibl v ∗
      (⌜ibl = value.ptr⌝ ∨
       ∃ (c : GoSlice), ⌜ibl = c.ptr⌝ ∗ c ↦* v ∗ ownSliceCap w8 c (DFrac.own 1)) }}

end spec

end bbolt
end EtcdGrove
end Perennial
