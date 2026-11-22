/-
Proof of `Spec/google_golang_org/grpc/WithTransportCredentials.lean` over the model's body (phase 7 S1, dial side,
2026-11-22, `notes/phase7-plan.md`; a trust-boundary axiom until grpc's translation was the model's,
`models/grpc`, which keeps grpc-go v1.84.0's `WithTransportCredentials`): its closure sets `copts.TransportCredentials`.
-/
module

public import Spec.google_golang_org.grpc.WithTransportCredentials

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
variable [package_sem : google_golang_org.grpc.Assumptions]

set_option goose.wp.extras true in
theorem grpc.WithTransportCredentials.wp_proof : grpc.WithTransportCredentials.spec (GF := GF) (hG := hG) := by
  intro creds
  wp_start
  iapply wp_fupd
  wp_auto
  ipersist creds
  wp_func_lits
  wp_func_call
  wp_call
  wp_auto
  ipersist «$r0»
  imodintro
  iapply HΦ
  unfold grpcDialOptIs dialOptFnOk
  iexists _, _
  isplitr
  · ipureintro; rfl
  isplitr
  · iexact «$r0»
  imodintro
  iintro %p %dopt %Ψ Hp HΨ
  wp_auto
  iapply HΨ $$ Hp
  ipureintro
  simp [dialOptsKeep, dialOptSets]

end proof

end EtcdGrove
end Perennial
