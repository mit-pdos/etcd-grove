/-
Trust boundary: `grpc.ChainStreamInterceptor` (an axiom; see `Spec/google_golang_org/grpc/ChainStreamInterceptor.lean`).
-/
module

public import Spec.google_golang_org.grpc.ChainStreamInterceptor

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

/-- **Trust boundary** (item 4, the server start): grpc's `ChainStreamInterceptor` returns a
`funcServerOption` whose `apply` appends the interceptors to `chainStreamInts` (read when
`NewServer` applies it). -/
axiom grpc.ChainStreamInterceptor.wp_proof : grpc.ChainStreamInterceptor.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
