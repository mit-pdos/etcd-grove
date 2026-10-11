/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/RemoteKV__Key.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.RemoteKV__Key

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

theorem RemoteKV.Key.wp_proof : RemoteKV.Key.spec (GF := GF) (hG := hG) := by
  intro rk st
  unfold ownRemoteKV RemoteKVSt.val'
  wp_start as Hrk
  wp_auto
  iapply HΦ
  iframe

end proof

end recipes
end EtcdGrove
end Perennial
