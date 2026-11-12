/-
Proof of `Spec/google_golang_org/grpc/WithStreamInterceptor.lean`: a trust-boundary axiom (item 5, client construction).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.google_golang_org.grpc.WithStreamInterceptor

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

/-- **Trust boundary** (item 5): `WithStreamInterceptor(f)` returns a `funcDialOption` that sets
`dopts.streamInt = f` (grpc v1.84.0). -/
axiom grpc.WithStreamInterceptor.wp_proof : grpc.WithStreamInterceptor.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
