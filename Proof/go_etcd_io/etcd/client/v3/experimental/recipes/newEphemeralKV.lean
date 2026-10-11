/-
Proof of `Spec/go_etcd_io/etcd/client/v3/experimental/recipes/newEphemeralKV.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.newEphemeralKV
public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.newKV
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Session__Client
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Session__Lease

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

theorem newEphemeralKV.wp_proof (hCl : concurrency.Session.Client.spec (GF := GF) (hG := hG))
    (hLe : concurrency.Session.Lease.spec (GF := GF) (hG := hG))
    (hNKV : newKV.spec (GF := GF) (hG := hG)) :
    newEphemeralKV.spec (GF := GF) (hG := hG) := by
  intro s γ client id pfx key val lo
  wp_start as ⟨#Hsess, #Hcl, #Hlo, %Hk⟩
  ihave #Hcp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency $$ []
  · iPkgInit
  ihave ⟨%kv, #HKV, #Hkv⟩ := isEtcdRecipesClient_kv client pfx $$ Hcl
  wp_auto
  wp_apply hCl s γ client id $$ [$Hcp $Hsess]
  (try wp_auto)
  wp_apply hLe s γ client id $$ [$Hcp $Hsess]
  (try wp_auto)
  wp_apply hNKV kv pfx key val id lo $$ [$Hpkg $Hkv $Hlo] as %rk %err Hres
  · ipureintro; exact Hk
  icases Hres with (⟨%Heq, %r, Hrk, #Hr, #Hc, %Hrr⟩ | ⟨#Herr, %Hrk, %r, #Hr, #Hp, %Hlr⟩ | %Hne)
  · subst Heq
    unfold ownRemoteKV RemoteKVSt.val'
    wp_auto
    wp_alloc ek as Hek
    iStructNamed Hek
    wp_auto
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists kv, r
    unfold ownEphemeralKV ownRemoteKV RemoteKVSt.val'
    iframe HKV Hr Hc
    iframe
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
    ipureintro; exact ⟨Hne, rfl⟩

end proof

end recipes
end EtcdGrove
end Perennial
