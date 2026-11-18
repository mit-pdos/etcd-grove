/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/NewClusterClient.lean`: an allocation. Lean-first.
-/
module

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

theorem NewClusterClient.wp_proof : NewClusterClient.spec (GF := GF) (hG := hG) := by
  intro cc
  wp_start
  wp_auto
  wp_alloc x as Hx
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
