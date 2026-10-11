module
public import Proof.go_etcd_io.bbolt.Init

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

/-- `t.DB()`: the field `db`. -/
abbrev Tx.DB.spec : Prop :=
  ∀ (tl : Loc) (t : Tx) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ tl ↦{dq} t }}
    (App (Val (tl @!! go.GoType.PointerType Tx.ty @!! go!"DB")) (Val #()))
  {{ RET #t.db'; tl ↦{dq} t }}

end spec

end bbolt
end EtcdGrove
end Perennial
