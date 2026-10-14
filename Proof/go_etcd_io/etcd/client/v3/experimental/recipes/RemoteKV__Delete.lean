/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/RemoteKV__Delete.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.RemoteKV__Delete
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
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

theorem RemoteKV.Delete.wp_proof (hTODO : EtcdGrove.context.TODO.spec (GF := GF) (hG := hG)) :
    RemoteKV.Delete.spec (GF := GF) (hG := hG) := by
  intro rk st pfx lo
  rcases st with ⟨kv, key, rev, val⟩
  unfold ownRemoteKV RemoteKVSt.val'
  wp_start as ⟨Hrk, #Hkv, #Hlo, %Hk⟩
  cases kv with
  | nil =>
    wp_auto
    iapply HΦ
    iframe Hrk
    ipureintro; rfl
  | ok kv =>
    simp only at Hk
    iunfold isRecipesKV at Hkv
    icases Hkv with ⟨-, -, #HDel, -⟩
    wp_auto
    wp_apply hTODO
    (try wp_auto)
    ihave #Hnil := concurrency.optsAt_nil (GF := GF)
    iunfold isEtcdDeleteKVTodo at HDel
    obtain ⟨hkk, hke⟩ := concurrency.deleteOp_fields key
    wp_apply HDel $$ %key %slice.nil %([] : List (OpFull → OpFull)) %lo [$Hnil $Hlo] as %resp %err #Hres
    · ipureintro
      refine ⟨concurrency.deleteOp_not_panics key, ?_⟩
      rw [hkk, hke]; exact concurrency.keyRangeUnder_key pfx key Hk
    (try wp_auto)
    iapply HΦ
    iframe Hrk
    iexact Hres

end proof

end recipes
end EtcdGrove
end Perennial
