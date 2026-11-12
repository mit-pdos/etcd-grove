/-
Proof of `Spec/google_golang_org/grpc/WithResolvers.lean`: a trust-boundary axiom (item 5, client construction).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.google_golang_org.grpc.WithResolvers

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

/-- **Trust boundary** (item 5): `WithResolvers(rs...)` returns a `funcDialOption` that appends
`rs` to `dopts.resolvers` (grpc v1.84.0). -/
axiom grpc.WithResolvers.wp_proof : grpc.WithResolvers.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
