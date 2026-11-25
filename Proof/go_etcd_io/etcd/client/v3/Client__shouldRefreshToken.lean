/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Client__shouldRefreshToken.lean` (unit P3a). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__shouldRefreshToken
public import Spec.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Error
public import Spec.errors.IsStatusErr

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk statusErrOk_nil backoffOk errorStringSpec)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem Client.shouldRefreshToken.wp_proof
    (wp_rpctypes_Error : rpctypes.Error.spec (GF := GF) (hG := hG))
    (wp_Is : errors.IsStatusErr.spec (GF := GF) (hG := hG)) :
    Client.shouldRefreshToken.spec (GF := GF) (hG := hG) := by
  intro c err o m
  wp_start as ⟨#Hc, #Ho, %Herr, #Hse, #Hm⟩
  obtain ⟨Hne, Hce⟩ := Herr
  ihave #Herrs : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Hrpc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
  · iPkgInit
  ihave Hri : (go_etcd_io.etcd.cache.v3.rpctypesInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hrpc
  icases Hri with ⟨-, -, -, -, -, ⟨%xUE, #HUE, %HdUE⟩, ⟨%xIA, #HIA, %HdIA⟩, ⟨%xAO, #HAO, %HdAO⟩, -⟩
  ihave #DUE := go_etcd_io.etcd.cache.v3.descIs_etcdError (GF := GF) xUE
  ihave #DIA := go_etcd_io.etcd.cache.v3.descIs_etcdError (GF := GF) xIA
  ihave #DAO := go_etcd_io.etcd.cache.v3.descIs_etcdError (GF := GF) xAO
  iunfold retryOptsAt at Ho
  icases Ho with ⟨%ov, #Hov, #Hovk⟩
  icases options_fields_ro o ov $$ Hov with ⟨#Hrp, #Hmax, #Hbf, #Hra⟩
  generalize ov.retryAuth' = ra
  iunfold retryClientOk at Hc
  icases Hc with ⟨%Hcn, #Hlg, %tok, %atb, #Htok, #Hatb, %Htokatb, -⟩
  wp_auto
  wp_if_destruct
  rotate_left
  · iapply HΦ; ipureintro; intro h; cases h
  wp_apply wp_rpctypes_Error err m $$ [$Hse $Hm] as %e1 ⟨%Hne1, #Hse1, -, #Hd1, -⟩
  · ipureintro; exact Hne
  wp_apply (wp_Is e1 _ (some (m, xUE.desc')) (Or.inl ⟨xUE, rfl⟩)) $$ [$Herrs $Hse1] as %b1 %Hb1
  · iapply go_etcd_io.etcd.cache.v3.isDescs_some $$ Hd1 DUE
  cases b1
  · wp_auto
    wp_if_destruct
    rotate_left
    · wp_apply wp_rpctypes_Error err m $$ [$Hse $Hm] as %e2 ⟨%Hne2, #Hse2, -, #Hd2, -⟩
      · ipureintro; exact Hne
      wp_apply (wp_Is e2 _ (some (m, xIA.desc')) (Or.inl ⟨xIA, rfl⟩)) $$ [$Herrs $Hse2] as %b2 %Hb2
      · iapply go_etcd_io.etcd.cache.v3.isDescs_some $$ Hd2 DIA
      cases b2
      · wp_auto
        wp_apply wp_rpctypes_Error err m $$ [$Hse $Hm] as %e3 ⟨%Hne3, #Hse3, -, #Hd3, -⟩
        · ipureintro; exact Hne
        wp_apply (wp_Is e3 _ (some (m, xAO.desc')) (Or.inl ⟨xAO, rfl⟩)) $$ [$Herrs $Hse3] as %b3 %Hb3
        · iapply go_etcd_io.etcd.cache.v3.isDescs_some $$ Hd3 DAO
        iapply HΦ
        by_cases hb : b3 = true
        · ihave %Hm3 := go_etcd_io.etcd.cache.v3.descIs_is_etcdError e3 xAO m ((Hb3 hb).1 _ _ rfl) $$ Hd3
          ipureintro; intro _
          rw [Hm3, HdAO]; simp [go_etcd_io.etcd.cache.v3.refusalDescs]
        · ipureintro; intro h; exact absurd h hb
      · wp_auto
        iapply HΦ
        ihave %Hm2 := go_etcd_io.etcd.cache.v3.descIs_is_etcdError e2 xIA m ((Hb2 rfl).1 _ _ rfl) $$ Hd2
        ipureintro; intro _
        rw [Hm2, HdIA]; simp [go_etcd_io.etcd.cache.v3.refusalDescs]
    · iapply HΦ; ipureintro; intro h; cases h
  · wp_auto
    ihave %Hm1 := go_etcd_io.etcd.cache.v3.descIs_is_etcdError e1 xUE m ((Hb1 rfl).1 _ _ rfl) $$ Hd1
    cases atb
    all_goals
      wp_auto
      iapply HΦ; ipureintro; intro _
      rw [Hm1, HdUE]; simp [go_etcd_io.etcd.cache.v3.refusalDescs]

end proof

end EtcdGrove
end Perennial
