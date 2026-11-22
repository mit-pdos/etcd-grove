/-
Proof of `Spec/go_etcd_io/etcd/client/v3/NewMaintenance.lean` (a trust-boundary axiom of item 5
until 2026-11-22). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.NewMaintenance
public import Spec.go_etcd_io.etcd.client.v3.Client__GetLogger
public import Spec.go_etcd_io.etcd.client.v3.RetryMaintenanceClient

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- The dial closure is only built (`maintenance.dial`), never called here. -/
theorem NewMaintenance.wp_proof (wp_GetLogger : Client.GetLogger.spec (GF := GF) (hG := hG))
    (wp_RetryMaintenanceClient : RetryMaintenanceClient.spec (GF := GF) (hG := hG)) :
    NewMaintenance.spec (GF := GF) (hG := hG) := by
  intro c
  wp_start as #Hc
  iunfold clientCoreAt at Hc
  icases Hc with ⟨%Hne, #Hlg, ⟨%conn, #Hconn⟩, ⟨%sl, #Hcopts⟩, -⟩
  wp_auto
  wp_apply wp_GetLogger c $$ [Hlg] as %lg -
  · iexact Hlg
  wp_apply wp_RetryMaintenanceClient c conn as %v ⟨%r, %Hv⟩
  subst Hv
  wp_func_lits
  wp_auto
  ihave %Hmpn := typedPointsto_not_null $$ «$r0»
  iStructNamed «$r0»
  simp only [decide_eq_false Hne]
  wp_auto
  iapply HΦ
  ipureintro
  exact ⟨_, Hmpn, rfl⟩

end proof

end EtcdGrove
end Perennial
