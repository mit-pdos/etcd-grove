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
    (hAI : EtcdServer.AuthInfoFromCtx.spec (GF := GF) (hG := hG))
    (hAS : EtcdServer.AuthStore.spec (GF := GF) (hG := hG)) :
    v3rpc.AuthAdmin.requireAuthInfo.spec (GF := GF) (hG := hG) := by
  intro aa s E ctx cd
  wp_start as ⟨#Haa, #Hctx, HRD⟩
  iunfold v3rpc.authAdminIs at Haa
  icases Haa with ⟨%Hann, #Hag, #Hau⟩
  iunfold srvAuthAt at Hau
  icases Hau with ⟨%st, %cca, %P, %f, #Has, #Hreq, #Hcca, #Hast⟩
  iunfold apply.isAuthStore at Hast
  icases Hast with ⟨%ai, %Hai, -, -, -, -, -, #HEn, -⟩
  subst Hai
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply (hAS s (GoInterface.ok ai))
  · iframe #
  (try wp_auto)
  wp_apply HEn $$ [$HRD] as %b ⟨HRD, #Hb⟩
  (try wp_auto)
  cases b
  · (try wp_auto)
    iapply HΦ
    iframe HRD
    iunfold authedOut
    isplitr
    · iapply applyErrIs_nil
    isplitr
    · ipureintro; intro _; rfl
    isplitr
    · iintro %_
      iexists none
      iapply (authedRes_of_disabled E.authMode none) $$ Hb
    · iintro %h; exact absurd rfl h
  · (try wp_auto)
    ihave %Hon := enabledVerdict_true_isOn E.authMode $$ Hb
    wp_apply (hAI s (GoInterface.ok ai) E.RD cca ctx cd) $$ [$HRD] as %a %err ⟨HRD, Ha, #Herr⟩
    · iframe #
    (try wp_auto)
    rcases err with ei | _
    · (try wp_auto)
      iapply HΦ
      iframe HRD
      iunfold authedOut
      isplitr
      · iexact Herr
      isplitr
      · ipureintro; intro h; rw [h] at Hon; cases Hon
      isplitr
      · iintro %h; cases h
      · iintro %_; iexact Hb
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
        (try wp_auto)
        iapply HΦ
        iframe HRD
        iunfold authedOut
        isplitr
        · iexact HaUE
        isplitr
        · ipureintro; intro h; rw [h] at Hon; cases Hon
        isplitr
        · iintro %h; cases h
        · iintro %_; iexact Hb
      · ihave #Hap := authInfoIs_pointsto a user rev $$ Hau
        iunfold authInfoIs at Hau
        icases Hau with ⟨%Hann', -, -⟩
        (try wp_auto)
        rw [_root_.decide_eq_false Hann']
        (try wp_auto)
        iapply HΦ
        iframe HRD
        iunfold authedOut
        isplitr
        · iapply applyErrIs_nil
        isplitr
        · ipureintro; intro _; rfl
        isplitr
        · iintro %_
          iexists (some { Username' := user, Revision' := rev })
          iapply authedRes_some
        · iintro %h; exact absurd rfl h

end proof

end EtcdGrove
end Perennial
