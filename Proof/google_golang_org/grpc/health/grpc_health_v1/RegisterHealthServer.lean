/-
Trust boundary: `grpc_health_v1.RegisterHealthServer` (an axiom; see `Spec/google_golang_org/grpc/health/grpc_health_v1/RegisterHealthServer.lean`).
-/
module

public import Spec.google_golang_org.grpc.health.grpc_health_v1.RegisterHealthServer

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

/-- **Trust boundary** (item 4, the server start): the generated `RegisterHealthServer` calls
`srv.testEmbeddedByValue()` (`*health.Server` embeds `UnimplementedHealthServer` by value: a no-op)
and `s.RegisterService(&Health_ServiceDesc, srv)`: the service `grpc.health.v1.Health` (`Check`,
`List`; the stream `Watch`), whose handler type `*health.Server` implements; the names are distinct
(`grpc.Server.RegisterService`'s spec). -/
axiom grpc_health_v1.RegisterHealthServer.wp_proof : grpc_health_v1.RegisterHealthServer.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
