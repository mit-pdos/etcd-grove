module
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsValidPage

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

/-- `p.FastCheck(id)` returns when the page has the id `id` and a valid type (otherwise it
panics). -/
abbrev Page.FastCheck.spec : Prop :=
  ∀ (l : Loc) (v : Page) (dq : DFrac) (id : w64),
  v.id' = id → validPageFlags v.flags' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ l ↦{dq} v }}
    (App (Val (l @!! go.GoType.PointerType Page.ty @!! go!"FastCheck")) (Val #id))
  {{ RET #(); l ↦{dq} v }}

end spec

end bbolt
end EtcdGrove
end Perennial
