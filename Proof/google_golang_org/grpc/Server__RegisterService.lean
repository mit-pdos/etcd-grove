/-
Trust boundary: `(*grpc.Server).RegisterService` (an axiom; see `Spec/google_golang_org/grpc/Server__RegisterService.lean`).
-/
module

public import Spec.google_golang_org.grpc.Server__RegisterService

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (item 4, the server start): grpc's `RegisterService` checks `ss` against
`sd.HandlerType` (`logger.Fatalf` if it does not implement it), then `register`: `logger.Fatalf` if
the server serves already (excluded: `grpcSrvNew` is given up by `grpc.start`) or the service name
is registered; otherwise it records `services[sd.ServiceName]` with `methods[d.MethodName] = d` for
each method and `streams[d.StreamName] = d` for each stream, and the server's `handleStream`
dispatches a call's path `/<service>/<method>` to them (a method's name before a stream's: the names
are distinct here). -/
axiom grpc.Server.RegisterService.wp_proof : grpc.Server.RegisterService.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
