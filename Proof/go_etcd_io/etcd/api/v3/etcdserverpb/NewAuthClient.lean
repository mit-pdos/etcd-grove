/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/NewAuthClient.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.NewAuthClient

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

theorem NewAuthClient.wp_proof : NewAuthClient.spec (GF := GF) (hG := hG) := by
  intro cc
  wp_start
  wp_auto
  wp_alloc ac as Hac
  iStructNamed Hac
  ipersist cc
  wp_auto
  iapply HΦ
  iexists ac
  iframe
  isplitl []
  · ipureintro; rfl
  · iexact cc

end proof

end EtcdGrove
end Perennial
