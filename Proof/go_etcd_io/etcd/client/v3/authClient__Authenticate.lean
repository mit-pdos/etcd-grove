/-
Proof of `Spec/go_etcd_io/etcd/client/v3/authClient__Authenticate.lean` (the auth plan's C1). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.authClient__Authenticate
public import Spec.go_etcd_io.etcd.client.v3.retryAuthClient__Authenticate
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

theorem authClient.Authenticate.wp_proof
    (wp_retry : retryAuthClient.Authenticate.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    authClient.Authenticate.spec (GF := GF) (hG := hG) := by
  intro api addr ci cd name pw Spec Q
  wp_start as ⟨#Hapi, #Hctx, #Hce, #Hrpc, #Hpre⟩
  iunfold authObjAt at Hapi
  icases Hapi with ⟨%rac, %conn, %sl, #Hremote, #Hrac, #Hconn, #Hcopts, #Hsl⟩
  wp_auto
  ihave Hsend : (pbAuthenticateRequest (GF := GF)).send «$a1_ptr» ⟨name, pw⟩ $$ [«$a1»]
  · simp only [pbAuthenticateRequest]
    iexists _
    iframe «$a1»
    ipureintro; exact ⟨rfl, rfl⟩
  iunfold callOptsAt at Hsl
  icases Hsl with ⟨%vs, #Hvs, -, #Hvok, -⟩
  wp_apply wp_retry rac conn addr Spec Q ci cd «$a1_ptr» ⟨name, pw⟩ sl vs $$ [Hsend]
    as %resp %err ⟨-, Hres⟩
  · iframe #
    iframe
  iunfold authnCallOut at Hres
  icases Hres with (⟨%Herr, Hq⟩ | ⟨%Herr, #Hse, #Hcl⟩)
  · subst Herr
    ihave #Hse0 := go_etcd_io.etcd.cache.v3.statusErrOk_nil (GF := GF)
    wp_apply wp_ContextError ci cd GoInterface.nil $$ [$Hse0] as %err' ⟨%Herr', -⟩
    · iframe #; ipureintro; exact fun h => (h rfl).elim
    obtain ⟨H1, -⟩ := Herr'
    rw [H1 rfl]
    iapply HΦ
    unfold authnCallOut
    ileft
    iframe
    ipureintro; rfl
  · obtain ⟨Hne, Hce', Hnull⟩ := Herr
    wp_apply wp_ContextError ci cd err $$ [$Hse] as %err' ⟨%Herr', #Hse', #Hclw⟩
    · iframe #; ipureintro; exact fun _ => Hce'
    ihave #Hcl' := Hclw $$ Hcl
    iapply HΦ
    unfold authnCallOut
    iright
    iframe #
    ipureintro
    exact ⟨(Herr'.2 Hne).1, (Herr'.2 Hne).2, Hnull⟩

end proof

end EtcdGrove
end Perennial
