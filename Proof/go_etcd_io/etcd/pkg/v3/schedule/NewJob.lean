/-
Proof of the spec of the same name: pending (mvcc's compaction, units 5b/5c; `sorry`).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.schedule.NewJob

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.schedule.Assumptions]

/-- Pending (mvcc's compaction, units 5b/5c). -/
theorem schedule.NewJob.wp_proof : schedule.NewJob.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
