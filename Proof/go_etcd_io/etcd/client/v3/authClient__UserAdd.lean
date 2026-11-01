/-
Proof of `Spec/go_etcd_io/etcd/client/v3/authClient__UserAdd.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.authClient__UserAdd
public import Spec.go_etcd_io.etcd.client.v3.retryAuthClient__UserAdd
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

theorem authClient.UserAdd.wp_proof
    (wp_retry : retryAuthClient.UserAdd.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    authClient.UserAdd.spec (GF := GF) (hG := hG) := by
  intro api conn addr ci cd name pw Spec Q
  wp_start as ⟨#Hapi, #Hctx, #Hce, #Hrpc, #Hpre, %Hsz⟩
  iunfold authObjAtC at Hapi
  icases Hapi with ⟨%rac, %sl, #Hremote, #Hrac, #Hconn, #Hcopts, #Hsl⟩
  wp_auto
  ihave %Hvn := typedPointsto_not_null _ _ _ $$ «$v2»
  ipersist «$v2»
  ihave #Hopt : userOptsFalse (GF := GF) «$v2_ptr» $$ []
  · unfold userOptsFalse auth.userOptsAt
    iright
    isplitr
    · ipureintro; exact Hvn
    iexists _, _, _
    iexact «$v2»
  ihave Hsend : (pbAuthUserAddRequest (GF := GF)).send «$a1_ptr» ⟨name, pw⟩ $$ [«$a1»]
  · simp only [pbAuthUserAddRequest]
    iexists _
    iframe «$a1»
    isplitr
    · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
    iexact Hopt
  iunfold callOptsAt at Hsl
  icases Hsl with ⟨%vs, #Hvs, -, #Hvok, -⟩
  wp_apply wp_retry rac conn addr Spec Q ci cd «$a1_ptr» ⟨name, pw⟩ sl vs $$ [Hsend]
    as %resp %err ⟨-, Hres⟩
  · iframe #
    iframe
    try (ipureintro; exact strsSizeOk.lt_2 Hsz)
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
