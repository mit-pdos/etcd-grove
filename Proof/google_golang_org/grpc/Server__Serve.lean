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

/-- **Trust boundary**. grpc-go v1.84's `Serve(lis)` (the model's
`Serve` → `handleRawConn` → `serveStreams` → `HandleStreams` → `handleStream` → `processRPC`) serves
every connection accepted on `lis`, and every byte it writes on a connection to `a` meets `a`'s
acceptor protocol (`grpcSrvPI Svc`) given that the dialer met `grpcCliPI Svc`: a unary call of a
method with an entry `e` runs Go's handler for it (`grpcServes`) on the request the call's deposit
holds, with the deposit `e.spec md m Φ Ψe` at the run's incoming metadata, and the reply's `Φ m'`
(or `Ψe d` for a handler's description `d`) is what the attempt gets back; a method without an entry
gets `Unimplemented`. A stream of a method with a
stream entry `e` runs Go's stream handler for it (`grpcServes`' stream clause) as `ClientConn.NewStream`'s
axiom pairs it: both ends share the stream's names `γ`; the dispatched metadata is an attempt's; the
client learns the dispatch `(a, md)` with each response (`streamDispIs`), and the handler is given `md`
through its context; the handler is given its specification at its content family, and its
responses' content converts to the entry's `dn₀ md γ`, which the client receives; messages are
delivered in order, intact, once; a server `SendMsg` after the status may return `nil` undelivered
(R3). A unary call of a stream's name and a stream of a unary method's name are excluded by the kind
clauses (C3 and its mirror). One run per deposit or stream: one stream per connection, dispatched
once; transparent retry only of a refused, undispatched first attempt; no retry policy
(`grpcResolverAt`). A head naming no entry is written only by `Invoke`/`NewStream`, which take an
entry. Both protocols are opaque: no program but grpc's transport reads or writes a connection to `a`
meaningfully, which is the model's claim "both ends run the model" (`models/README.md`). Under
`grpcRepliesFit`, or (grpc-trusted-T, T9, 2026-11-24; retired by decision B's W3) with every reply a
handler of `Svc` can send bounded by its registered model (`grpcRepliesBounded Svc`: a reply a handler
sends is one its reply model's `send` holds of, `grpcServes`, `grpcRunOkMd`, the stream run's `SendMsg`;
below `grpcReplyMax` it marshals). -/
axiom grpc.Server.Serve.wp_proof : grpc.Server.Serve.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
