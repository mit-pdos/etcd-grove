module
public import Proof.go_etcd_io.bbolt.BucketOpen
public import Spec.go_etcd_io.bbolt.newBucket

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section defs
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext]

/-- The bucket `openBucket` returns in a write transaction `txl`: its header at `ibl` (a copy),
its inline page at `pgl` (for an inline bucket), its caches `bm`, `nm`. -/
def wOpenedOf (txl ibl pgl : Loc) (bm nm : GoMap) (v : List w8) : Bucket :=
  Bucket.mk ibl txl bm (if inBucketRoot v = 0 then pgl else null) null nm defaultFillPercent

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `b.openBucket(value)` in a write transaction: a new bucket whose header is a copy of the
value's (a new `InBucket`, or the start of a copy of the value when it is unaligned), its
inline page the value's bytes after the header (of the value itself, or of the copy, whose
bytes are handed out). -/
abbrev Bucket.openBucket.wspec : Prop :=
  ∀ (bl : Loc) (bv : Bucket) (dqb dqw : DFrac) (value : GoSlice) (v : List w8) (dv : DFrac),
  16 ≤ v.length → (inBucketRoot v = 0 → 16 < v.length) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ bl ↦{dqb} bv ∗
      structFieldRef Tx go!"writable" bv.tx' ↦{dqw} true ∗ value ↦*{dv} v }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"openBucket")) (Val #value))
  {{ (cl ibl pgl : Loc) (bm nm : GoMap), RET #cl; bl ↦{dqb} bv ∗
      structFieldRef Tx go!"writable" bv.tx' ↦{dqw} true ∗ value ↦*{dv} v ∗
      cl ↦ wOpenedOf bv.tx' ibl pgl bm nm v ∗ ibl ↦ ibOf v ∗
      bm ↦$ (∅ : GMap GoString Loc) ∗ nm ↦$ (∅ : GMap w64 Loc) ∗
      (⌜pgl = value.ptr +ₗ 16⌝ ∨ bytesPointsto pgl (DFrac.own 1) (v.drop 16)) }}

end spec

end bbolt
end EtcdGrove
end Perennial
