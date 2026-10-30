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

/-- `p.Meta()`: the location just after the page header (16 bytes), where a meta page
keeps its `Meta`. -/
abbrev Page.Meta.spec : Prop :=
  ∀ (l : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common }}
    (App (Val (l @!! go.GoType.PointerType Page.ty @!! go!"Meta")) (Val #()))
  {{ RET #(l +ₗ 16); True }}

end spec

end bbolt
end EtcdGrove
end Perennial
