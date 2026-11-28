/-
Proof of `Spec/google_golang_org/grpc/StatsHandler.lean` over the model's body (2026-11-26,
`notes/axiom-review/grpc-statshandler.md`; a trust-boundary axiom until then; the model,
`models/grpc`, keeps grpc-go v1.84.0's `StatsHandler`): of a non-nil handler, its closure skips the
logging branch and appends the handler to `statsHandlers`, an option of the kind `.stats h`.
-/
module

public import Spec.google_golang_org.grpc.StatsHandler

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
theorem grpc.StatsHandler.wp_proof : grpc.StatsHandler.spec (GF := GF) (hG := hG) := by
  intro hv
  wp_start as %Hh
  obtain ⟨Hnn, Hok⟩ := Hh
  cases hv with
  | nil => exact absurd rfl Hnn
  | ok hi =>
    iapply wp_fupd
    wp_auto
    ipersist h
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
    isplitr
    · ipureintro; exact Hok
    imodintro
    iintro %p %so %hs %Ψ Hp Hhs Hcap HΨ
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply (wp_slice_append (V := GoInterface) _ hs _ [interface.ok hi] _) $$ [$Hhs $Hcap $Hsl] as %ns ⟨Hns, Hncap, _⟩
    have Hif : (if interface.ok hi = interface.nil then ([] : List GoInterface)
        else [interface.ok hi]) = [interface.ok hi] := by simp
    rw [Hif]
    iapply HΨ $$ Hp Hns Hncap
    ipureintro
    exact ⟨(by unfold srvOptsSameBut; rfl), rfl, rfl, rfl⟩

end proof

end EtcdGrove
end Perennial
