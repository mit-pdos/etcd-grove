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

/-- `tx.Size()`: the database size the transaction sees, its meta's high-water mark in pages
times the page size. -/
abbrev Tx.Size.spec : Prop :=
  ∀ (tl : Loc) (t : Tx) (m : internal.common.Meta) (d : DB) (dq1 dq2 dq3 : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ tl ↦{dq1} t ∗ t.meta' ↦{dq2} m ∗ t.db' ↦{dq3} d }}
    (App (Val (tl @!! go.GoType.PointerType Tx.ty @!! go!"Size")) (Val #()))
  {{ RET #(m.pgid' * d.pageSize'); tl ↦{dq1} t ∗ t.meta' ↦{dq2} m ∗ t.db' ↦{dq3} d }}

end spec

end bbolt
end EtcdGrove
end Perennial
