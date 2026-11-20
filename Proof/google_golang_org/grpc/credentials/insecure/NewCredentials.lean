/-
Proof of `Spec/google_golang_org/grpc/credentials/insecure/NewCredentials.lean` over the real body
(prove-grpcsmall, 2026-11-20; a trust-boundary axiom while `insecure` was names only): `insecureTC{}`
as `credentials.TransportCredentials`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.google_golang_org.grpc.credentials.insecure.NewCredentials

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.credentials.insecure.Assumptions]

theorem insecure.NewCredentials.wp_proof : insecure.NewCredentials.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
