/-
Proof of `gone.spec` (leaseexpiryN's `gone` proof, `Proof/.../examples/etcd/leaseexpiryN/gone.lean`, over the
dist listing `leaseList.specLive`): each poll sleeps, lists at the lower bound `m`; a listing without `id`
is a snapshot at an index `j ≥ m` without it (`leaseIdsAt`), i.e. `leaseAbsentFrom … m id`; a listing's
error polls again.
Lean-first (no Rocq counterpart); #50 N9b (`notes/etcd-dist-n9b.md`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.gone
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.leaseList
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.listed
public import Perennial.Spec.time.Sleep
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Net client
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open etcd_dist.view

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [esrv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

set_option maxHeartbeats 800000 in
theorem gone.wp_proof
    (wp_leaseList : leaseList.specLive (GF := GF) (hG := hG))
    (wp_listed : listed.spec (GF := GF) (hG := hG))
    (wp_Sleep : time.Sleep.spec (GF := GF) (hG := hG)) :
    gone.spec (GF := GF) (hG := hG) := by
  intro π cl ep V Γ mid m id hAs hlm
  wp_start as ⟨Hlt, #Hmc, #Hlb⟩
  ihave #Ptime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  (try wp_auto)
  ihave IO : (∃ (n : w64), "i" ∷ i_ptr ↦ n ∗ "Hlt" ∷ levelTok 0 : IProp GF) $$ [i Hlt]
  · iexists _; iframe
  wp_for IO
  wp_if_destruct
  · (try wp_auto)
    wp_apply wp_Sleep
    (try wp_auto)
    -- the listing, at the lower bound `m`
    wp_apply (wp_leaseList cl ep V Γ mid m hAs hlm) $$ [$Hlt] as %ls %lerr ⟨Hlt, Hls⟩
    · iframe #
    icases Hls with (⟨%Hlerr, %ids, %sl, %j, #Hslf, Hsl, %Hmj, #Hids⟩ | %Hlfail)
    · subst Hlerr
      imod ownSlice_persist _ _ _ $$ Hsl with #Hsl
      (try wp_auto)
      wp_apply (wp_listed ls sl ids id) $$ []
      · iframe #
      by_cases hin : id ∈ ids
      · rw [decide_eq_true hin]
        (try wp_auto)
        wp_for_post
        iframe
        iexists _; iframe
      · rw [decide_eq_false hin]
        (try wp_auto)
        wp_for_post
        iapply HΦ
        iframe Hlt
        simp only [↓reduceIte]
        iunfold lease.leaseIdsAt at Hids
        icases Hids with ⟨%τ, %Hτ, #Hτat⟩
        iunfold lease.leaseAbsentFrom
        iexists j, τ
        iframe Hτat
        ipureintro
        refine ⟨Hmj, ?_⟩
        cases h : τ.1.lookup id with
        | none => rfl
        | some _ => exact absurd ((Hτ.2 id).2 (by rw [h]; rfl)) hin
    · obtain ⟨Hlerr, -⟩ := Hlfail
      cases lerr with
      | nil => exact absurd rfl Hlerr
      | ok ei => ?_
      (try wp_auto)
      wp_for_post
      iframe
      iexists _; iframe
  · (try wp_auto)
    iapply HΦ; iframe Hlt; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
