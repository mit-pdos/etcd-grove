/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Client__shouldRefreshToken.lean` (unit P3a). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrDesc
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem Client.shouldRefreshToken.wp_proof
    (wp_rpctypes_Error : rpctypes.Error.spec (GF := GF) (hG := hG))
    (wp_Is : errors.IsStatusErr.spec (GF := GF) (hG := hG)) :
    Client.shouldRefreshToken.spec (GF := GF) (hG := hG) := by
  intro c err o
  wp_start as ⟨#Hc, #Ho, %Herr, #Hse⟩
  obtain ⟨Hne, Hce⟩ := Herr
  ihave #Herrs : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Hrpc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
  · iPkgInit
  ihave Hri : (go_etcd_io.etcd.cache.v3.rpctypesInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hrpc
  icases Hri with ⟨-, -, -, -, -, ⟨%xUE, #HUE, %HdUE⟩, ⟨%xIA, #HIA, %HdIA⟩, ⟨%xAO, #HAO, %HdAO⟩, -⟩
  iunfold retryOptsAt at Ho
  icases Ho with ⟨%ov, #Hov, #Hovk⟩
  icases options_fields_ro o ov $$ Hov with ⟨#Hrp, #Hmax, #Hbf, #Hra⟩
  generalize ov.retryAuth' = ra
  iunfold retryClientOk at Hc
  icases Hc with ⟨%Hcn, #Hlg, %tok, %atb, #Htok, #Hatb, %Htokatb⟩
  wp_auto
  wp_if_destruct
  rotate_left
  · iapply HΦ; ipureintro; intro h; cases h
  wp_apply wp_rpctypes_Error err $$ [$Hse] as %e1 ⟨%Hne1, #Hse1, -, %Hd1, -⟩
  · ipureintro; exact Hne
  wp_apply (wp_Is e1 _ (Or.inl ⟨xUE, rfl⟩)) $$ [$Herrs $Hse1] as %b1 %Hb1
  cases b1
  · wp_auto
    wp_if_destruct
    rotate_left
    · wp_apply wp_rpctypes_Error err $$ [$Hse] as %e2 ⟨%Hne2, #Hse2, -, %Hd2, -⟩
      · ipureintro; exact Hne
      wp_apply (wp_Is e2 _ (Or.inl ⟨xIA, rfl⟩)) $$ [$Herrs $Hse2] as %b2 %Hb2
      cases b2
      · wp_auto
        wp_apply wp_rpctypes_Error err $$ [$Hse] as %e3 ⟨%Hne3, #Hse3, -, %Hd3, -⟩
        · ipureintro; exact Hne
        wp_apply (wp_Is e3 _ (Or.inl ⟨xAO, rfl⟩)) $$ [$Herrs $Hse3] as %b3 %Hb3
        iapply HΦ; ipureintro; intro h
        rw [← Hd3, Hb3 h, rpctypes.errDesc_etcdError, HdAO]; simp [go_etcd_io.etcd.cache.v3.refusalDescs]
      · wp_auto
        iapply HΦ; ipureintro; intro _
        rw [← Hd2, Hb2 rfl, rpctypes.errDesc_etcdError, HdIA]; simp [go_etcd_io.etcd.cache.v3.refusalDescs]
    · iapply HΦ; ipureintro; intro h; cases h
  · wp_auto
    cases atb
    all_goals
      wp_auto
      iapply HΦ; ipureintro; intro _
      rw [← Hd1, Hb1 rfl, rpctypes.errDesc_etcdError, HdUE]; simp [go_etcd_io.etcd.cache.v3.refusalDescs]

end proof

end EtcdGrove
end Perennial
