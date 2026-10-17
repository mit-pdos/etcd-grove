/-
Trust boundary: otelgrpc's `NewServerHandler` (an axiom; see `Spec/go_opentelemetry_io/contrib/instrumentation/google_golang_org/grpc/otelgrpc/NewServerHandler.lean`).
-/
module

public import Spec.go_opentelemetry_io.contrib.instrumentation.google_golang_org.grpc.otelgrpc.NewServerHandler

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

/-- **Trust boundary** (item 4, the server start): `NewServerHandler` applies its options
(`otelgrpc.Option`: an interface with an unexported method, so otelgrpc's own, which set its
configuration) and returns a `*serverHandler`: its `TagRPC` returns the call's context with a span
and otelgrpc's own values (its keys, not etcd's), `HandleRPC` records; neither stops a call. -/
axiom otelgrpc.NewServerHandler.wp_proof : otelgrpc.NewServerHandler.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
