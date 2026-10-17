/-
The trust boundary: `Scheduler.Pending` (the FIFO scheduler's methods are names-only).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.schedule.Scheduler__Pending

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

axiom schedule.Scheduler.Pending.wp_proof : schedule.Scheduler.Pending.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
