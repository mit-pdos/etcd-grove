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

/-- **Trust boundary** (unit P3a: the interceptors are no longer inside it; its meaning restated at
phase 7 S2's interface, 2026-11-24, its text unchanged): a unary call through grpc's `ClientConn` is
its interceptor chain (`chainWP`, as `chainUnaryClientInterceptors` composes it) over grpc's `invoke`,
which makes one attempt (`grpcInvokerOk`). An attempt dials one of `addrs`, `a₀`. `a₀`'s table, set
once at the start (a bridge's address: to its target's table, `bridge.New`), has an entry for `method` at the
attempt's registered message models (`grpcSvcAt`, inside `isGrpcRpcsMd`, no heap). The attempt
converts the caller's `Spec md m Φ Ψe` into the entry's spec by `grpcSvcAt`'s update; the handler's
view of the metadata is an attempt's (`grpcAttemptMd`). It writes as
`a₀`'s dialer protocol says (`grpcCliPI`, opaque: no program but grpc's transport writes a connection
to a grpc address meaningfully). On success it returns the `Φ m'` that the server's protocol
delivers, which `Server.Serve`'s axiom guarantees (`grpc.Server.Serve.wp_proof`: the server runs the
entry's handler on the deposit). A dial before any listener exists is grpc's `Unavailable` error,
whose description is not a handler's. The deposit goes to at most one run, as before: one stream per
connection, dispatched once; transparent retry only of a refused, undispatched stream; no retry
policy (`grpcResolverAt`); an error can return while the run is still pending or running (test T2).
Reviewed in `notes/axiom-review/s2-interface.md` (until S2's interface: the deposit was the
registration `isGrpcRpcAt` at the address's server, paired with the model `Serve`'s `acceptRun`). -/
axiom grpc.ClientConn.Invoke.wp_proof : grpc.ClientConn.Invoke.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
