module
public import Spec.go_etcd_io.bbolt.internal.common.UnsafeAdd

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

/-- `p.BranchPageElements()`: the page's `count` elements, as a slice of `branchPageElement`s over the page after its
header (16 bytes each); `nil` if there are none. -/
abbrev Page.BranchPageElements.spec : Prop :=
  ∀ (l : Loc) (v : Page) (dq : DFrac),
  l.locCar ≠ 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v }}
    (App (Val (l @!! go.GoType.PointerType Page.ty @!! go!"BranchPageElements")) (Val #()))
  {{ RET #(if v.count' = W16 0 then slice.nil
           else slice.mk (l +ₗ 16) (W64 (uint.Z v.count')) (W64 (uint.Z v.count')));
      l ↦{dq} v }}

end spec

end bbolt
end EtcdGrove
end Perennial
