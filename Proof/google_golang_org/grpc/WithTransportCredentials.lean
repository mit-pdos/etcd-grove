/-
Proof of `Spec/google_golang_org/grpc/WithTransportCredentials.lean`: a trust-boundary axiom (item 5, client construction).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.google_golang_org.grpc.WithTransportCredentials

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

/-- **Trust boundary** (item 5): `WithTransportCredentials(creds)` returns a `funcDialOption` that
sets `dopts.copts.TransportCredentials = creds` (grpc v1.84.0). -/
axiom grpc.WithTransportCredentials.wp_proof : grpc.WithTransportCredentials.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
