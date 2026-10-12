/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/RWMutex__RUnlock.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.RWMutex__RUnlock
public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.RemoteKV__Delete

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

theorem RWMutex.RUnlock.wp_proof (wp_Delete : RemoteKV.Delete.spec (GF := GF) (hG := hG)) :
    RWMutex.RUnlock.spec (GF := GF) (hG := hG) := by
  intro m pfx ek st lo
  unfold rwMyKey
  wp_start as ⟨⟨Hmk, Hek, #Hkv, %Hk⟩, #Hlo⟩
  wp_auto
  unfold ownEphemeralKV
  wp_apply wp_Delete _ st pfx lo $$ [$Hek $Hkv $Hlo] as %err ⟨Hek, Hres⟩
  · ipureintro; exact Hk
  iapply HΦ
  simp only
  iframe Hmk Hek
  isplitr
  · unfold isRecipesKV
    isplitr
    · itrivial
    ipureintro; exact Hk
  unfold rwUnlockResult
  rcases hkv : st.kv with kv | _
  · simp only
    iunfold deleteResult at Hres
    icases Hres with (%Hne | ⟨%Hnil, %r, %s, #Hr, %Hrs, #Hst⟩)
    · ileft; ipureintro; exact Hne
    iright
    isplitr
    · ipureintro; exact Hnil
    iexists r
    iframe Hr
    isplitr
    · iapply concurrency.deleteTxn_absent pfx st.key r s $$ Hst
    ipureintro; exact Hrs.1
  · simp only
    iexact Hres

end proof

end recipes
end EtcdGrove
end Perennial
