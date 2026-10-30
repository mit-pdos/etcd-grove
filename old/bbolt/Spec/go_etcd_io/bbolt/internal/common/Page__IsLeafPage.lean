module
public import Proof.go_etcd_io.bbolt.internal.common.Init

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

/-- `p.IsLeafPage()`: the page is a leaf page (its flags are exactly `2`). -/
abbrev Page.IsLeafPage.spec : Prop :=
  ∀ (l : Loc) (v : Page) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v }}
    (App (Val (l @!! go.GoType.PointerType Page.ty @!! go!"IsLeafPage")) (Val #()))
  {{ RET #(decide (v.flags' = W16 2)); l ↦{dq} v }}

end spec

end bbolt
end EtcdGrove
end Perennial
