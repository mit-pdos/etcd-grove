/-
The trust boundary: `Scheduler.Schedule` (the FIFO scheduler's methods are names-only).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.schedule.Scheduler__Schedule

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

axiom schedule.Scheduler.Schedule.wp_proof : schedule.Scheduler.Schedule.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
