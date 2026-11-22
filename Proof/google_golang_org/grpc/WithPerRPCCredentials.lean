/-
Proof of `Spec/google_golang_org/grpc/WithPerRPCCredentials.lean` over the model's body (phase 7 S1,
dial side, 2026-11-22, `notes/phase7-plan.md`; a trust-boundary axiom until grpc's translation was
the model's, `models/grpc`, which keeps grpc-go v1.84.0's `WithPerRPCCredentials`): its closure
appends the credentials to `copts.PerRPCCredentials`.
-/
module

public import Spec.google_golang_org.grpc.WithPerRPCCredentials

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
theorem grpc.WithPerRPCCredentials.wp_proof :
    grpc.WithPerRPCCredentials.spec (GF := GF) (hG := hG) := by
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
  iintro %p %dopt %cs %Ψ Hp Hcs Hcap HΨ
  wp_auto
  wp_apply wp_slice_literal (V := GoInterface) (l := [creds])
  isplitr
  · ipureintro; rfl
  iintro %l1 ⟨Hl1, -⟩
  wp_auto
  wp_apply (wp_slice_append (V := GoInterface) _ cs _ [creds] _) $$ [$Hcs $Hcap $Hl1]
    as %ns ⟨Hns, Hncap, _⟩
  iapply HΨ $$ Hp Hns Hncap
  ipureintro
  simp [dialOptsKeep, dialOptSets]

end proof

end EtcdGrove
end Perennial
