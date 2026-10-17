/-
Proof of `Spec/google_golang_org/grpc/credentials/insecure/NewCredentials.lean`: a trust-boundary axiom (item 5, client construction).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.google_golang_org.grpc.credentials.insecure.NewCredentials

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

/-- **Trust boundary** (item 5): `insecure.NewCredentials()` returns `insecureTC{}` as
`credentials.TransportCredentials`. -/
axiom insecure.NewCredentials.wp_proof : insecure.NewCredentials.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
