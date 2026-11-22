/-
Proof of `Spec/google_golang_org/grpc/WithResolvers.lean` over the model's body (phase 7 S1, dial side,
2026-11-22, `notes/phase7-plan.md`; a trust-boundary axiom until grpc's translation was the model's,
`models/grpc`, which keeps grpc-go v1.84.0's `WithResolvers`): its closure appends the builders to `resolvers`.
-/
module

public import Spec.google_golang_org.grpc.WithResolvers

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
theorem grpc.WithResolvers.wp_proof : grpc.WithResolvers.spec (GF := GF) (hG := hG) := by
  intro sl rbs
  wp_start as #Hsl
  iapply wp_fupd
  wp_auto
  ipersist rs
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
  iintro %p %dopt %us %Ψ Hp Hus Hcap HΨ
  wp_auto
  wp_apply (wp_slice_append (V := GoInterface) _ us _ rbs _) $$ [$Hus $Hcap $Hsl] as %ns ⟨Hns, Hncap, _⟩
  iapply HΨ $$ Hp Hns Hncap
  ipureintro
  simp [dialOptsKeep, dialOptSets]

end proof

end EtcdGrove
end Perennial
