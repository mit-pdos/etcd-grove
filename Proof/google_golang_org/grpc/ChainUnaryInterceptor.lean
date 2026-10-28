/-
Trust boundary: `grpc.ChainUnaryInterceptor` (an axiom; see `Spec/google_golang_org/grpc/ChainUnaryInterceptor.lean`).
-/
module

public import Spec.google_golang_org.grpc.ChainUnaryInterceptor

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

/-- **Trust boundary** (item 4, the server start): grpc's `ChainUnaryInterceptor` returns a
`funcServerOption` whose `apply` appends the interceptors to `chainUnaryInts` (the slice is read
when `NewServer` applies it: read-only here, so the same `ics`). -/
axiom grpc.ChainUnaryInterceptor.wp_proof : grpc.ChainUnaryInterceptor.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
