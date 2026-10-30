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

/-- `db.Info()`: a new `Info` with the address of the mapping and the page size (the file
must be mapped: else it panics). -/
abbrev DB.Info.spec : Prop :=
  ∀ (dbl : Loc) (d : DB) (dq : DFrac),
  d.data' ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ dbl ↦{dq} d }}
    (App (Val (dbl @!! go.GoType.PointerType DB.ty @!! go!"Info")) (Val #()))
  {{ (p : Loc), RET #p; p ↦ (Info.mk (ptrAddr d.data') d.pageSize') ∗ dbl ↦{dq} d }}

end spec

end bbolt
end EtcdGrove
end Perennial
