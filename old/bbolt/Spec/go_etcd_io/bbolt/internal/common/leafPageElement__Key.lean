module
public import Spec.go_etcd_io.bbolt.internal.common.UnsafeByteSlice

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

/-- `n.Key()`: the element's key, `ksize` bytes at `uint.Z v.pos'` after the element (in its
page), as a slice into the page. It panics if the end passes `MaxAllocSize`. -/
abbrev leafPageElement.Key.spec : Prop :=
  ∀ (l : Loc) (v : leafPageElement) (dq : DFrac),
  l.locCar ≠ 0 → uint.Z v.pos' + uint.Z v.ksize' ≤ 2147483647 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v }}
    (App (Val (l @!! go.GoType.PointerType leafPageElement.ty @!! go!"Key")) (Val #()))
  {{ RET #(slice.mk (l +ₗ uint.Z v.pos') (W64 (uint.Z v.ksize')) (W64 (uint.Z v.ksize')));
      l ↦{dq} v }}

end spec

end bbolt
end EtcdGrove
end Perennial
