/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/newKV.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.newKV
public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.putNewKV

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

theorem newKV.wp_proof (hPNK : putNewKV.spec (GF := GF) (hG := hG)) :
    newKV.spec (GF := GF) (hG := hG) := by
  intro kv pfx key val lease lo
  wp_start as ⟨#Hkv, #Hlo, %Hk⟩
  wp_auto
  wp_apply hPNK kv pfx key val lease lo $$ [$Hpkg $Hkv $Hlo] as %rev %err Hres
  · ipureintro; exact Hk
  icases Hres with (⟨%Heq, #Hr, #Hc, -, %Hrr⟩ | ⟨#Herr, %Hrev, %r, #Hr, #Hp, %Hlr⟩ | ⟨%Hne, #Hce⟩)
  · subst Heq
    wp_auto
    wp_alloc rk as Hrk
    wp_auto
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists rev
    unfold ownRemoteKV RemoteKVSt.val'
    iframe Hrk Hr Hc
    ipureintro; exact Hrr
  · ihave %Hne : ⌜err ≠ GoInterface.nil⌝ $$ [Herr]
    · unfold concurrency.isPkgErr; icases Herr with ⟨-, %H⟩; ipureintro; exact H
    obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
      cases err with
      | nil => exact absurd rfl Hne
      | ok e => exact ⟨e, rfl⟩
    wp_auto
    iapply HΦ
    iright; ileft
    iframe Herr
    isplitr
    · ipureintro; rfl
    iexists r
    iframe Hr Hp
    ipureintro; exact Hlr
  · obtain ⟨Hne, -⟩ := Hne
    obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
      cases err with
      | nil => exact absurd rfl Hne
      | ok e => exact ⟨e, rfl⟩
    wp_auto
    iapply HΦ
    iright; iright
    iframe Hce
    ipureintro; exact ⟨Hne, rfl⟩

end proof

end recipes
end EtcdGrove
end Perennial
