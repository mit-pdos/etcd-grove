/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/Barrier__Hold.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.Barrier__Hold
public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.newKey
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

theorem Barrier.Hold.wp_proof (hNK : newKey.spec (GF := GF) (hG := hG)) :
    Barrier.Hold.spec (GF := GF) (hG := hG) := by
  intro b client key lo
  wp_start as ⟨#Hb, #Hlo⟩
  iunfold isBarrier at Hb
  icases Hb with ⟨#Hbc, -, #Hbk, #Hcl⟩
  ihave ⟨%kv, #Hkvf, #Hkv⟩ := isEtcdRecipesClient_kv $$ Hcl
  wp_auto
  wp_apply hNK kv key key (W64 0) lo $$ [$Hpkg $Hkv $Hlo] as %rk %err Hres
  · ipureintro; exact List.prefix_refl key
  icases Hres with (⟨%Heq, %r, -, #Hr, #Hc, %Hrr⟩ | ⟨#Herr, %Hrk, %r, #Hr, #Hp, %Hlr⟩ | %Hne)
  · subst Heq
    (try wp_auto)
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists r
    iframe Hr Hc
    ipureintro; exact Hrr.1
  · (try wp_auto)
    iapply HΦ
    iright; ileft
    iframe Herr
    iexists r
    iframe Hr Hp
    ipureintro; exact Hlr
  · (try wp_auto)
    iapply HΦ
    iright; iright
    ipureintro; exact Hne.1

end proof

end recipes
end EtcdGrove
end Perennial
