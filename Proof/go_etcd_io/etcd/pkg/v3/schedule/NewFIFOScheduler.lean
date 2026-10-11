/-
The trust boundary: `schedule.NewFIFOScheduler` (`pkg/v3/schedule` is names-only; it starts the
scheduler's goroutine and returns the scheduler).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.schedule.NewFIFOScheduler

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom schedule.NewFIFOScheduler.wp_proof : schedule.NewFIFOScheduler.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
