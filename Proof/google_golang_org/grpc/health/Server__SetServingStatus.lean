/-
Trust boundary: `(*health.Server).SetServingStatus` (an axiom; see `Spec/google_golang_org/grpc/health/Server__SetServingStatus.lean`).
-/
module

public import Spec.google_golang_org.grpc.health.Server__SetServingStatus

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (item 4, the server start): grpc's `SetServingStatus` locks the server's
mutex, records the status (unless the server is shutting down) and notifies the service's watchers
(non-blocking sends to buffered channels, replacing a pending update): it returns, touching only the
server. -/
axiom health.Server.SetServingStatus.wp_proof : health.Server.SetServingStatus.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
