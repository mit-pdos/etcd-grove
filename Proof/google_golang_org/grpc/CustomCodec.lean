/-
Proof of `Spec/google_golang_org/grpc/CustomCodec.lean` over the model's body (W1, 2026-11-26; until
then a trust-boundary axiom, `notes/axiom-review/phase7-w1.md`): its closure stores
`newCodecV0Bridge(c)`, the value `codecV0Bridge{codec: c}` (as `any`), in `codec` and changes no other
field, a neutral option (`srvCodecOk`'s second disjunct, by the premise `grpcProtoCodec c`).
-/
module

public import Spec.google_golang_org.grpc.CustomCodec

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
theorem grpc.CustomCodec.wp_proof : grpc.CustomCodec.spec (GF := GF) (hG := hG) := by
  intro c
  wp_start as %Hc
  iapply wp_fupd
  wp_auto
  ipersist codec
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
  wp_func_call
  wp_call
  wp_auto
  iapply HΨ $$ Hp
  ipureintro
  refine ⟨rfl, Or.inr ⟨c, Hc, rfl⟩, rfl, rfl, rfl⟩

end proof

end EtcdGrove
end Perennial
