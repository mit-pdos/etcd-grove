/-
`clientv3.NewCluster(c)` (`cluster.go`: `&cluster{remote: RetryClusterClient(c), callOpts:
c.callOpts}`), verified: translated with its body (`Code/go_etcd_io/etcd/client/v3.toml`). Until
2026-11-18 a trust-boundary axiom (item 5, client construction). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.NewCluster
public import Spec.go_etcd_io.etcd.client.v3.RetryClusterClient

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

theorem NewCluster.wp_proof
    (wp_RetryClusterClient : RetryClusterClient.spec (GF := GF) (hG := hG)) :
    NewCluster.spec (GF := GF) (hG := hG) := by
  intro c
  wp_start as #Hc
  iunfold clientCoreAt at Hc
  icases Hc with ⟨%Hnn, _, ⟨%conn, #Hconn⟩, ⟨%sl, #Hsl⟩, _⟩
  wp_auto
  wp_apply (wp_RetryClusterClient c conn) as %v -
  · iexact Hconn
  iStructNamed «$r0»
  rw [show decide (c = null) = false from decide_eq_false Hnn]
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
