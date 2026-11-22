/-
Proof of `Spec/go_etcd_io/etcd/client/v3/NewCluster.lean` (a trust-boundary axiom of item 5 until
2026-11-22). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.NewCluster
public import Spec.go_etcd_io.etcd.client.v3.RetryClusterClient

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

theorem NewCluster.wp_proof (wp_RetryClusterClient : RetryClusterClient.spec (GF := GF) (hG := hG)) :
    NewCluster.spec (GF := GF) (hG := hG) := by
  intro c
  wp_start as #Hc
  iunfold clientCoreAt at Hc
  icases Hc with ⟨%Hne, -, ⟨%conn, #Hconn⟩, ⟨%sl, #Hcopts⟩, -⟩
  wp_auto
  wp_apply wp_RetryClusterClient c conn $$ [] as %v ⟨%r, %Hv⟩
  · iexact Hconn
  subst Hv
  iStructNamed «$r0»
  simp only [decide_eq_false Hne]
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
