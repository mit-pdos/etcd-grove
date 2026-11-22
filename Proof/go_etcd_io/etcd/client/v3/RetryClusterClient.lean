/-
Proof of `Spec/go_etcd_io/etcd/client/v3/RetryClusterClient.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.RetryClusterClient
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.NewClusterClient

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

theorem RetryClusterClient.wp_proof (wp_NewClusterClient : NewClusterClient.spec (GF := GF) (hG := hG)) :
    RetryClusterClient.spec (GF := GF) (hG := hG) := by
  intro cl conn
  wp_start as #Hconn
  wp_auto
  wp_apply wp_NewClusterClient as %v ⟨%ac, %Hv, -⟩
  subst Hv
  wp_alloc r as Hr
  wp_auto
  iapply HΦ
  iexists r
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial
