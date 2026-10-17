/-
Trust boundary: `grpc.NewServer` (an axiom; see `Spec/google_golang_org/grpc/NewServer.lean`).
-/
module

public import Spec.google_golang_org.grpc.NewServer

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

/-- **Trust boundary** (item 4, the server start): grpc's `NewServer` applies each option to its
`serverOptions` (`opt.apply(&opts)`), in order: `ChainUnaryInterceptor(ics...)` appends `ics` to
`chainUnaryInts`, `ChainStreamInterceptor` to `chainStreamInts`; then `chainUnaryServerInterceptors`
and `chainStreamServerInterceptors` compose them (no `UnaryInterceptor`/`StreamInterceptor` option:
the chain is that list); the other options (`.neutral`) set limits, credentials, the codec, stats
handlers. No service is registered; it does not serve until `Serve`. -/
axiom grpc.NewServer.wp_proof : grpc.NewServer.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
