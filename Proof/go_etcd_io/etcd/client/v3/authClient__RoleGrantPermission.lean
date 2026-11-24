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
  intro api conn addr ci om cd name key rangeEnd permType Spec Q
  wp_start as ⟨Hlt, #Hapi, #Hctx, #Hce, %Hkl, #Hrpc, #Hom, #Hpre, %Hsz⟩
  iunfold authObjAtC at Hapi
  icases Hapi with ⟨%rac, %sl, #Hremote, #Hrac, #Hconn, #Hcopts, #Hsl⟩
  wp_auto
  wp_apply wp_string_to_bytes key as %ksl ⟨Hksl, -⟩
  try wp_auto
  wp_apply wp_string_to_bytes rangeEnd as %rsl ⟨Hrsl, -⟩
  try wp_auto
  ihave %Hpn := typedPointsto_not_null _ _ _ $$ «$r0»
  ipersist Hksl
  ipersist Hrsl
  imod auth.ownPermW_freeze ⊤ «$r0_ptr» ⟨permType, key, rangeEnd⟩ _ ksl rsl _ [] _
    $$ [«$r0»] with #Hpw
  · iframe «$r0» Hksl Hrsl
    isplitr
    · ipureintro; exact ⟨Hpn, Hkl⟩
    iapply ownSlice_nil
  ihave Hsend : (pbAuthRoleGrantPermissionRequest (GF := GF)).send «$a1_ptr»
      (name, ⟨permType, key, rangeEnd⟩) $$ [«$a1»]
  · simp only [pbAuthRoleGrantPermissionRequest]
    iexists _
    iframe «$a1»
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    iexact Hpw
  iunfold callOptsAt at Hsl
  icases Hsl with ⟨%vs, #Hvs, -, #Hvok, -⟩
  wp_apply wp_retry rac conn addr Spec Q ci om cd «$a1_ptr» (name, ⟨permType, key, rangeEnd⟩) sl vs
    $$ [Hlt Hsend] as %resp %err ⟨Hlt, -, Hres⟩
  · iframe #
    iframe
    try (ipureintro; exact strsSizeOk.lt_3 Hsz)
  iunfold authCallOut at Hres
  icases Hres with (⟨%Herr, Hq⟩ | ⟨%Herr, #Hse, #Hcl⟩)
  · subst Herr
    ihave #Hse0 := go_etcd_io.etcd.cache.v3.statusErrOk_nil (GF := GF)
    ihave ⟨%mC, #HmC⟩ := go_etcd_io.etcd.cache.v3.statusErrOk_descIs _ $$ Hse0
    wp_apply wp_ContextError ci cd GoInterface.nil mC $$ [$Hse0 $HmC] as %err' ⟨%Herr', -, -⟩
    · iframe #; ipureintro; exact fun h => (h rfl).elim
    obtain ⟨H1, -⟩ := Herr'
    rw [H1 rfl]
    iapply HΦ
    iframe Hlt
    unfold authCallOut
    ileft
    iframe
    ipureintro; rfl
  · obtain ⟨Hne, Hce', Hnull⟩ := Herr
    ihave ⟨%mC, #HmC⟩ := go_etcd_io.etcd.cache.v3.statusErrOk_descIs _ $$ Hse
    wp_apply wp_ContextError ci cd err mC $$ [$Hse $HmC] as %err' ⟨%Herr', #Hse', #Hclw, -⟩
    · iframe #; ipureintro; exact fun _ => Hce'
    ihave #Hcl' := Hclw $$ Hcl
    iapply HΦ
    iframe Hlt
    unfold authCallOut
    iright
    iframe #
    ipureintro
    exact ⟨(Herr'.2 Hne).1, (Herr'.2 Hne).2, Hnull⟩

end proof

end EtcdGrove
end Perennial
