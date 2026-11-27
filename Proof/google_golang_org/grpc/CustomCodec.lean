/-
Proof of `Spec/google_golang_org/grpc/CustomCodec.lean` over the model's body (grpc-mem, 2026-11-26;
a trust-boundary axiom until `baseCodec` was translated: its methods name `mem.BufferSlice`, and grpc
now imports `mem`): `CustomCodec(c)`'s closure stores `newCodecV0Bridge(c)`, the value
`codecV0Bridge{codec: c}` as a `baseCodec` and then as `any`, in `codec` and in no other field: the
second disjunct of `srvCodecOk`, a neutral option.
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
  exact ⟨(by unfold srvOptsSameBut; rfl), (by unfold srvCodecOk; exact Or.inr ⟨c, Hc, rfl⟩),
    rfl, rfl, rfl⟩

end proof

end EtcdGrove
end Perennial
