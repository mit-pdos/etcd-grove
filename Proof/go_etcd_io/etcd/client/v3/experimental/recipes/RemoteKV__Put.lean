/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/RemoteKV__Put.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.RemoteKV__Put
public import Spec.context.TODO
public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRecipesLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

theorem RemoteKV.Put.wp_proof (hTODO : EtcdGrove.context.TODO.spec (GF := GF) (hG := hG)) :
    RemoteKV.Put.spec (GF := GF) (hG := hG) := by
  intro rk st kv pfx val lo
  rcases st with ⟨kv', key, rev, v0⟩
  unfold ownRemoteKV RemoteKVSt.val'
  wp_start as ⟨Hrk, %Hkv', #Hkv, #Hlo, %Hk⟩
  simp only at Hkv' Hk
  subst Hkv'
  iunfold isRecipesKV at Hkv
  icases Hkv with ⟨-, -, -, #HPut⟩
  wp_auto
  wp_apply hTODO
  (try wp_auto)
  ihave #Hnil := concurrency.optsAt_nil (GF := GF)
  iunfold isEtcdPutKVTodo at HPut
  wp_apply HPut $$ %key %val %slice.nil %([] : List (OpFull → OpFull)) %(TxnOp.put key val (W64 0)) %lo [$Hnil $Hlo] as %resp %err Hres
  · ipureintro
    exact ⟨putOp_not_panics' key val, putOp_txnOpOf' key val, Hk⟩
  (try wp_auto)
  iapply HΦ
  iframe Hrk
  iexact Hres

end proof

end recipes
end EtcdGrove
end Perennial
