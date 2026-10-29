/-
Proof of `Spec/go_etcd_io/etcd/client/v3/authClient__RoleGrantPermission.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.authClient__RoleGrantPermission
public import Spec.go_etcd_io.etcd.client.v3.retryAuthClient__RoleGrantPermission
public import Spec.go_etcd_io.etcd.client.v3.ContextError

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem authClient.RoleGrantPermission.wp_proof
    (wp_retry : retryAuthClient.RoleGrantPermission.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    authClient.RoleGrantPermission.spec (GF := GF) (hG := hG) := by
  intro api conn addr ci cd name key rangeEnd permType Spec Q
  wp_start as ⟨#Hapi, #Hctx, #Hce, %Hkl, #Hrpc, #Hpre⟩
  iunfold authObjAtC at Hapi
  icases Hapi with ⟨%rac, %sl, #Hremote, #Hrac, #Hconn, #Hcopts, #Hsl⟩
  wp_auto
  wp_apply wp_string_to_bytes key as %ksl ⟨Hksl, -⟩
  try wp_auto
  wp_apply wp_string_to_bytes rangeEnd as %rsl ⟨Hrsl, -⟩
  try wp_auto
  ihave %Hpn := typedPointsto_not_null _ _ _ $$ «$r0»
  ipersist «$r0»
  ipersist Hksl
  ipersist Hrsl
  ihave Hsend : (pbAuthRoleGrantPermissionRequest (GF := GF)).send «$a1_ptr»
      (name, ⟨permType, key, rangeEnd⟩) $$ [«$a1»]
  · simp only [pbAuthRoleGrantPermissionRequest]
    iexists _
    iframe «$a1»
    isplitr
    · ipureintro; rfl
    unfold auth.ownPermW
    isplitr
    · ipureintro; exact ⟨Hpn, Hkl⟩
    iexists _, _, _, _, _
    iframe #
  iunfold callOptsAt at Hsl
  icases Hsl with ⟨%vs, #Hvs, -, #Hvok, -⟩
  wp_apply wp_retry rac conn addr Spec Q ci cd «$a1_ptr» (name, ⟨permType, key, rangeEnd⟩) sl vs
    $$ [Hsend] as %resp %err ⟨-, Hres⟩
  · iframe #
    iframe
  iunfold authCallOut at Hres
  icases Hres with (⟨%Herr, Hq⟩ | ⟨%Herr, #Hse, #Hcl⟩)
  · subst Herr
    ihave #Hse0 := go_etcd_io.etcd.cache.v3.statusErrOk_nil (GF := GF)
    wp_apply wp_ContextError ci cd GoInterface.nil $$ [$Hse0] as %err' ⟨%Herr', -⟩
    · iframe #; ipureintro; exact fun h => (h rfl).elim
    obtain ⟨H1, -⟩ := Herr'
    rw [H1 rfl]
    iapply HΦ
    unfold authCallOut
    ileft
    iframe
    ipureintro; rfl
  · obtain ⟨Hne, Hce', Hnull⟩ := Herr
    wp_apply wp_ContextError ci cd err $$ [$Hse] as %err' ⟨%Herr', #Hse', #Hclw⟩
    · iframe #; ipureintro; exact fun _ => Hce'
    ihave #Hcl' := Hclw $$ Hcl
    iapply HΦ
    unfold authCallOut
    iright
    iframe #
    ipureintro
    exact ⟨(Herr'.2 Hne).1, (Herr'.2 Hne).2, Hnull⟩

end proof

end EtcdGrove
end Perennial
