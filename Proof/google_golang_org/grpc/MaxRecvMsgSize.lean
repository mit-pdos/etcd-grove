/-
Proof of `Spec/google_golang_org/grpc/MaxRecvMsgSize.lean` over the model's body (phase 7 S1, 2026-11-21,
`notes/phase7-plan.md`; a trust-boundary axiom until grpc's translation was the model's,
`models/grpc`, which keeps grpc-go v1.84.0's `MaxRecvMsgSize`): its closure sets `maxReceiveMessageSize`, a neutral option.
-/
module

public import Spec.google_golang_org.grpc.MaxRecvMsgSize

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
theorem grpc.MaxRecvMsgSize.wp_proof : grpc.MaxRecvMsgSize.spec (GF := GF) (hG := hG) := by
  intro n
  wp_start
  iapply wp_fupd
  wp_auto
  ipersist m
  wp_func_lits
  wp_func_call
  wp_call
  wp_auto
  ipersist «$r0»
  imodintro
  iapply HΦ
  unfold grpcSrvOpt srvOptFnOk
  iexists _, _
  isplitr
  · ipureintro; rfl
  isplitr
  · iexact «$r0»
  imodintro
  iintro %p %so %Ψ Hp HΨ
  wp_auto
  iapply HΨ $$ Hp
  ipureintro
  exact ⟨(by unfold srvOptsSameBut; rfl), (by unfold srvCodecOk; exact Or.inl rfl), rfl, rfl, rfl⟩

end proof

end EtcdGrove
end Perennial
