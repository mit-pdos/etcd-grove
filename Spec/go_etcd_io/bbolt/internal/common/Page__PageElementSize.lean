module
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsLeafPage

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

/-- `p.PageElementSize()`: 16, the size of a leaf and of a branch page element alike. -/
abbrev Page.PageElementSize.spec : Prop :=
  ∀ (l : Loc) (v : Page) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v }}
    (App (Val (l @!! go.GoType.PointerType Page.ty @!! go!"PageElementSize")) (Val #()))
  {{ RET #(W64 16); l ↦{dq} v }}

end spec

end bbolt
end EtcdGrove
end Perennial
