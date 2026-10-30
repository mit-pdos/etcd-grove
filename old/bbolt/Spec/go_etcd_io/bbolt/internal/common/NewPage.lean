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

/-- `NewPage(id, flags, count, overflow)`: a new page header. -/
abbrev NewPage.spec : Prop :=
  ∀ (id : w64) (flags count : w16) (overflow : w32),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common }}
    (App (App (App (App (Val #(functions NewPage [])) (Val #id)) (Val #flags)) (Val #count)) (Val #overflow))
  {{ (l : Loc), RET #l; l ↦ (Page.mk id flags count overflow) }}

end spec

end bbolt
end EtcdGrove
end Perennial
