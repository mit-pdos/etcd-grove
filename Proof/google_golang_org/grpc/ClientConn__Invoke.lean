/-
**Trust boundary**: grpc's `(*ClientConn).Invoke` of any unary method, as the connection's
unary interceptor chain over grpc's one-attempt `invoke` (an axiom; see
`Spec/google_golang_org/grpc/ClientConn__Invoke.lean` and `notes/decisions.md`, "A generic gRPC
specification", "The retry interceptor proved: the gRPC boundary below it").
-/
module

public import Spec.google_golang_org.grpc.ClientConn__Invoke

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
variable [peer_sem : google_golang_org.grpc.peer.Assumptions]

/-- **Trust boundary** (unit P3a: the interceptors are no longer inside it): a unary call
through grpc's `ClientConn` is its interceptor chain (`chainWP`, as `chainUnaryClientInterceptors`
composes it) over grpc's `invoke`, which makes one attempt (`grpcInvokerOk`: the network, grpc's
client and server, the protobuf codec, the server's runtime; a run of the handler served for the
method on a copy of the request, whose reply the client receives as a copy, or an error). -/
axiom grpc.ClientConn.Invoke.wp_proof : grpc.ClientConn.Invoke.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
