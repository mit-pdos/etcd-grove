/-
The proof of `Spec/google_golang_org/grpc/Server__Serve.lean`: a trust-boundary axiom (phase 7 S2's
interface, 2026-11-24; per-type stage B, B1b, to then a theorem over the trusted model
`Server.Serve.impl := model.Serve` and its leaves' axioms, `acceptRun`, `acceptRunConns`, `respond`,
`finishStream`, now retired). Reviewed in `notes/axiom-review/s2-interface.md`.
-/
module

public import Spec.google_golang_org.grpc.Server__Serve

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

/-- **Trust boundary** (phase 7 S2's interface, 2026-11-24; until then a theorem over the trusted
model `Server.Serve.impl` and its leaves, now retired). grpc-go v1.84's `Serve(lis)` (the model's
`Serve` → `handleRawConn` → `serveStreams` → `HandleStreams` → `handleStream` → `processRPC`) serves
every connection accepted on `lis`, and every byte it writes on a connection to `a` meets `a`'s
acceptor protocol (`grpcSrvPI Svc`) given that the dialer met `grpcCliPI Svc`: a unary call of a
method with an entry `e` runs Go's handler for it (`grpcServes`) on the request the call's deposit
holds, with the deposit `e.spec md m Φ Ψe` at the run's incoming metadata, and the reply's `Φ m'`
(or `Ψe d` for a handler's description `d`) is what the attempt gets back; a method without an entry
gets `Unimplemented`; a stream runs as the stream pair states (`InvGrpcRun.lean`, "The pair": the
registrations `isGrpcStreamAt γ` of a started server, the only ones `NewStream` takes). One run per
deposit: one stream per connection, dispatched once; transparent retry only of a refused,
undispatched stream; no retry policy (`grpcResolverAt`). Both protocols are opaque: no program but
grpc's transport reads or writes a connection to `a` meaningfully, which is the model's claim "both
ends run the model" (`models/README.md`). Under `grpcRepliesFit`. -/
axiom grpc.Server.Serve.wp_proof : grpc.Server.Serve.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
