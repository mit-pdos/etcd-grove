/-
`clientv3.NewMaintenance(c)` (`maintenance.go`: `&maintenance{lg: c.GetLogger(), dial: <a closure
over c>, remote: RetryMaintenanceClient(c, c.conn)}`, then `callOpts`), verified: translated with
its body (`Code/go_etcd_io/etcd/client/v3.toml`); the `dial` closure is only built. Until
2026-11-18 a trust-boundary axiom (item 5, client construction). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.NewMaintenance
public import Spec.go_etcd_io.etcd.client.v3.RetryMaintenanceClient
public import Spec.go_etcd_io.etcd.client.v3.Client__GetLogger

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
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem NewMaintenance.wp_proof
    (wp_GetLogger : Client.GetLogger.spec (GF := GF) (hG := hG))
    (wp_RetryMaintenanceClient : RetryMaintenanceClient.spec (GF := GF) (hG := hG)) :
    NewMaintenance.spec (GF := GF) (hG := hG) := by
  intro c
  wp_start as #Hc
  iunfold clientCoreAt at Hc
  icases Hc with ⟨%Hnn, #Hlg, ⟨%conn, #Hconn⟩, ⟨%sl, #Hsl⟩, _⟩
  wp_auto
  wp_apply wp_GetLogger as %lg -
  · iexact Hlg
  wp_apply wp_RetryMaintenanceClient as %v -
  try wp_auto
  rw [recv_eq_func_mk]
  wp_auto
  icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨Hr, %Hrnn⟩
  iStructNamed Hr
  rw [show decide (c = null) = false from decide_eq_false Hnn]
  wp_auto
  iapply HΦ
  ipureintro
  exact ⟨_, Hrnn, rfl⟩

end proof

end EtcdGrove
end Perennial
