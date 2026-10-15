/-
`job.Name` (`pkg/schedule/schedule.go`), translated with its body. Lean-first (2026-10-13, mvcc's
compaction, unit 5a).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.schedule.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.schedule.Assumptions]

/-- `j.Name()` returns the job's name. -/
abbrev schedule.job.Name.spec : Prop :=
  ∀ (jv : go_etcd_io.etcd.pkg.v3.schedule.job),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule }}
    (App (Val (jv @!! go_etcd_io.etcd.pkg.v3.schedule.job.ty @!! go!"Name")) (Val #()))
  {{ RET #(jv.name'); True }}

end spec

end EtcdGrove
end Perennial
