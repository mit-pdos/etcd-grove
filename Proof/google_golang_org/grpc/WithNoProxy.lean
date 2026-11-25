/-
Proof of `Spec/google_golang_org/grpc/WithNoProxy.lean` over the model's body (2026-11-24,
`notes/putget-dist-plan.md` §12, finding F1; `models/grpc` keeps grpc-go v1.84.0's `WithNoProxy`): its
closure sets `useProxy` to `false`. As `WithTransportCredentials.lean`.
-/
module

public import Spec.google_golang_org.grpc.WithNoProxy

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
theorem grpc.WithNoProxy.wp_proof : grpc.WithNoProxy.spec (GF := GF) (hG := hG) := by
  wp_start
  iapply wp_fupd
  wp_auto
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
