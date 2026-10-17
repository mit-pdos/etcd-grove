/-
Proof of `Spec/google_golang_org/grpc/WithUnaryInterceptor.lean`: a trust-boundary axiom (item 5, client construction).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.google_golang_org.grpc.WithUnaryInterceptor

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

/-- **Trust boundary** (item 5): `WithUnaryInterceptor(f)` returns a `funcDialOption` that sets
`dopts.unaryInt = f` (grpc v1.84.0). -/
axiom grpc.WithUnaryInterceptor.wp_proof : grpc.WithUnaryInterceptor.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
