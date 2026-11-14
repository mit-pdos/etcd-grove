/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthAdmin__requireAuthInfo
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AuthInfoFromCtx
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AuthStore
@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.AuthAdmin.requireAuthInfo.wp_proof
    (hAI : EtcdServer.AuthInfoFromCtx.specLb (GF := GF) (hG := hG))
    (hAS : EtcdServer.AuthStore.spec (GF := GF) (hG := hG)) :
    v3rpc.AuthAdmin.requireAuthInfo.spec (GF := GF) (hG := hG) := by
  intro aa s E ctx cd n
  wp_start as ⟨#Haa, #Hlb, #Hctx, #Hlib, HRD⟩
  iunfold v3rpc.authAdminIs at Haa
  icases Haa with ⟨%Hann0, #Hag, #Hau⟩
  iunfold srvAuthAt at Hau
  icases Hau with ⟨%st, %cca, #Has, #Hreq, #Hreqb, #Hcca, #Hast⟩
  iunfold apply.isAuthStore at Hast
  icases Hast with ⟨%ai, %Hai, -, -, -, -, -, #HEn, -⟩
  subst Hai
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply (hAS s (GoInterface.ok ai))
  · iframe #
  (try wp_auto)
  ihave #HEnLb := isAuthEnabled_ctxMLb (GoInterface.ok ai) E.RD E.authMode ai rfl n $$ [$HEn $Hreqb $Hlb]
  wp_apply HEnLb $$ [$HRD] as %b ⟨HRD, #Hb, #HbLb⟩
  (try wp_auto)
  cases b
  · (try wp_auto)
    iapply HΦ
    iframe HRD
    iunfold authedOutC
    isplitr
    · iunfold authedOutB
      isplitr
      · iapply applyErrIs_nil
      isplitr
      · ipureintro; intro _; rfl
      isplitr
      · iintro %_
        iexists none
        isplitl
        · iapply (authedRes_of_disabled E.authMode none) $$ Hb
        iintro !> -; iunfold principalBound; itrivial
      · iintro %h; exact absurd rfl h
    · iintro %h; exact absurd rfl h
  · (try wp_auto)
    ihave %Hon := enabledVerdict_true_isOn E.authMode $$ Hb
    ihave #HbLb' := HbLb $$ %Hon
    wp_apply (hAI s (GoInterface.ok ai) E.RD E.authMode cca ctx cd n)
      $$ [$HRD] as %a %err ⟨HRD, Ha, #Herr0, #Hbnd, #Hae, #Hz, #Hne⟩
    · iframe #
    ihave #Herr := authApplyErrIs_apply _ $$ Herr0
    ihave #Hbnd : ctxBoundOrTLS s E.authMode (GoInterface.ok ctx) a $$ []
    · iapply Hbnd; ipureintro; exact Hon
    ihave #Hz' := Hz $$ %Hon
    ihave #Hne' := Hne $$ %Hon
    (try wp_auto)
    rcases err with ei | _
    · (try wp_auto)
      iapply HΦ
      iframe HRD
      iunfold authedOutC
      isplitr
      · iunfold authedOutB
        isplitr
        · iexact Herr
        isplitr
        · ipureintro; intro h; rw [h] at Hon; cases Hon
        isplitr
        · iintro %h; cases h
        · iintro %_; iexact Hb
      · iintro %hne
        iapply (authedWhy_of_reqSide E.authMode n _ _)
        iunfold reqSideWhy
        ihave ⟨#Hit, #Hen', #Htk⟩ := Hne' $$ %hne
        iframe Hen'
        iright
        iframe Hit Htk
    · (try wp_auto)
      iunfold authInfoOpt at Ha
      icases Ha with (%Han | ⟨%user, %rev, Hau⟩)
      · subst Han
        (try wp_auto)
        ihave #Hpauth : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth $$ []
        · iPkgInit
        ihave #Hainit : go_etcd_io.etcd.server.v3.auth.authInit (GF := GF) $$ []
        · iapply isPkgInit_access $$ Hpauth
        icases Hainit with ⟨#HUE, -⟩
        ihave #HUEl := errVarLeaf_authErrVar _ $$ HUE
        ihave ⟨%eUE, #HeUE, #HaUE⟩ := errVarLeaf_get _ $$ HUEl
        ihave #HaaUE := apply.authErrVar_authApplyErrIs go_etcd_io.etcd.server.v3.auth.ErrUserEmpty
          (by simp [go_etcd_io.etcd.server.v3.auth.authErrMsgs]) (GoInterface.ok eUE) $$ HUE
          [HeUE]
        · iexists eUE; iframe HeUE; ipureintro; rfl
        iunfold authApplyErrIs at HaaUE
        icases HaaUE with ⟨-, #HvUE⟩
        (try wp_auto)
        iapply HΦ
        iframe HRD
        iunfold authedOutC
        isplitr
        · iunfold authedOutB
          isplitr
          · iexact HaUE
          isplitr
          · ipureintro; intro h; rw [h] at Hon; cases Hon
          isplitr
          · iintro %h; cases h
          · iintro %_; iexact Hb
        · iintro %_
          iapply (authedWhy_of_reqSide E.authMode n _ _)
          iunfold reqSideWhy
          iframe HbLb'
          ileft
          isplitr
          · iunfold auth.authErrOf; iexists eUE; simp only [auth.AuthErr.var]; iframe HeUE
          · iapply Hz'; exact ⟨rfl, rfl⟩
      · ihave #Hpb := principalBound_of_ctxBoundOrTLS s E.authMode (GoInterface.ok ctx) a user rev $$ [$Hbnd $Hau]
        iunfold authInfoIs at Hau
        icases Hau with ⟨%Hann, -, -⟩
        (try wp_auto)
        rw [_root_.decide_eq_false Hann]
        (try wp_auto)
        iapply HΦ
        iframe HRD
        iunfold authedOutC
        isplitr
        · iunfold authedOutB
          isplitr
          · iapply applyErrIs_nil
          isplitr
          · ipureintro; intro _; rfl
          isplitr
          · iintro %_
            iexists (some { Username' := user, Revision' := rev })
            isplitl
            · iapply authedRes_some
            iintro !> -; iexact Hpb
          · iintro %h; exact absurd rfl h
        · iintro %h; exact absurd rfl h


end proof

end EtcdGrove
end Perennial
