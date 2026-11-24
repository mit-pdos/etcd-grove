/-
Proof of `Spec/go_etcd_io/etcd/client/v3/authClient__UserGrantRole.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.authClient__UserGrantRole
public import Spec.go_etcd_io.etcd.client.v3.retryAuthClient__UserGrantRole
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

theorem authClient.UserGrantRole.wp_proof
    (wp_retry : retryAuthClient.UserGrantRole.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    authClient.UserGrantRole.spec (GF := GF) (hG := hG) := by
  intro api conn addr ci om cd user role Spec Q
  wp_start as ⟨Hlt, #Hapi, #Hctx, #Hce, #Hrpc, #Hom, #Hpre, %Hsz⟩
  iunfold authObjAtC at Hapi
  icases Hapi with ⟨%rac, %sl, #Hremote, #Hrac, #Hconn, #Hcopts, #Hsl⟩
  wp_auto
  ihave Hsend : (pbAuthUserGrantRoleRequest (GF := GF)).send «$a1_ptr» (user, role) $$ [«$a1»]
  · simp only [pbAuthUserGrantRoleRequest]
    iexists _
    iframe «$a1»
    ipureintro; exact ⟨rfl, rfl, rfl⟩
  iunfold callOptsAt at Hsl
  icases Hsl with ⟨%vs, #Hvs, -, #Hvok, -⟩
  wp_apply wp_retry rac conn addr Spec Q ci om cd «$a1_ptr» (user, role) sl vs $$ [Hlt Hsend]
    as %resp %err ⟨Hlt, -, Hres⟩
  · iframe #
    iframe
    try (ipureintro; exact strsSizeOk.lt_2 Hsz)
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
