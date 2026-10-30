module
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__IsBucketEntry
public import Spec.go_etcd_io.bbolt.internal.common.leafPageElement__Value
public import Spec.go_etcd_io.bbolt.internal.common.LoadBucket

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `n.Bucket()`: for a bucket entry, its value's header (`LoadBucket(n.Value())`), else
`nil`. A bucket entry's value must not be empty (it panics otherwise). -/
abbrev leafPageElement.Bucket.spec : Prop :=
  ∀ (l : Loc) (v : leafPageElement) (dq : DFrac),
  l.locCar ≠ 0 → uint.Z v.pos' + uint.Z v.ksize' + uint.Z v.vsize' ≤ 2147483647 →
  (v.flags' &&& W32 1 ≠ W32 0 → 0 < uint.Z v.vsize') →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v }}
    (App (Val (l @!! go.GoType.PointerType leafPageElement.ty @!! go!"Bucket")) (Val #()))
  {{ RET #(if v.flags' &&& W32 1 ≠ W32 0 then l +ₗ (uint.Z v.pos' + uint.Z v.ksize') else null);
      l ↦{dq} v }}

end spec

end bbolt
end EtcdGrove
end Perennial
