/-
The proof of `Spec/google_golang_org/grpc/Server__Serve.lean`: `Serve`'s body is the trusted model,
whose spec `Proof/google_golang_org/grpc/model/Serve.lean` proves.
-/
module

public import Spec.google_golang_org.grpc.Server__Serve
public import Spec.google_golang_org.grpc.model.Serve
public import GeneratedProof.google_golang_org.grpc

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
variable [package_sem : google_golang_org.grpc.Assumptions]

/-- **`Serve` meets its spec** (per-type stage B, B1b; it was an axiom): its body is the trusted model
(`Server.Serve.impl := model.Serve`), whose spec is proved over its leaves' axioms. -/
theorem grpc.Server.Serve.wp_proof (hS : grpc.model.Serve.spec (GF := GF) (hG := hG)) :
    grpc.Server.Serve.spec (GF := GF) (hG := hG) := by
  intro gs lis γ
  wp_start_folded as Htok
  wp_method_call
  unfold google_golang_org.grpc.Server.Serve.impl
  wp_pure
  iapply (hS gs lis γ) $$ Htok
  iintro %err
  inext
  iintro -
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
