/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/RemoteKV__Value.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.RemoteKV__Value

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

theorem RemoteKV.Value.wp_proof : RemoteKV.Value.spec (GF := GF) (hG := hG) := by
  intro rk st
  unfold ownRemoteKV RemoteKVSt.val'
  wp_start as ⟨Hrk, %Hkl⟩
  wp_auto
  iapply HΦ
  iframe
  ipureintro; exact Hkl

end proof

end recipes
end EtcdGrove
end Perennial
