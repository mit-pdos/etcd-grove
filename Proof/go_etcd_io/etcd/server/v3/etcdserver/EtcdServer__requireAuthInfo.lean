/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__requireAuthInfo.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__requireAuthInfo
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AuthInfoFromCtx
@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- One proof for both modes (the auth-mode merge, 2026-10-29: the former `wp_proof` and
`requireAuthInfo_bound`): `AuthInfoFromCtx` is called only with auth on, where the gate is open. -/
theorem EtcdServer.requireAuthInfo.wp_proof
    (hAI : EtcdServer.AuthInfoFromCtx.spec (GF := GF) (hG := hG)) :
    EtcdServer.requireAuthInfo.spec (GF := GF) (hG := hG) := by
  intro s E ctx cd
  wp_start as ⟨#Hau, #Hctx, HRD⟩
  iunfold srvAuthAt at Hau
  icases Hau with ⟨%st, %cca, %P, %f, #Has, #Hreq, #Hreqb, #Hcca, #Hast⟩
  iunfold apply.isAuthStore at Hast
  icases Hast with ⟨%ai, %Hai, -, -, -, -, -, #HEn, -⟩
  subst Hai
  (try wp_auto)
  wp_apply HEn $$ [$HRD] as %b ⟨HRD, #Hb⟩
  (try wp_auto)
  cases b
  · (try wp_auto)
    iapply HΦ
    iframe HRD
    iunfold authedOutB
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
  · (try wp_auto)
    ihave %Hon := enabledVerdict_true_isOn E.authMode $$ Hb
    wp_apply (hAI s (GoInterface.ok ai) E.RD E.authMode cca ctx cd)
      $$ [$HRD] as %a %err ⟨HRD, Ha, #Herr, #Hbnd⟩
    · iframe #
    -- auth on here (`Hon`): the binding's gate open
    ihave #Hbnd : ctxBoundOrTLS s E.authMode (GoInterface.ok ctx) a $$ []
    · iapply Hbnd; ipureintro; exact Hon
    (try wp_auto)
    rcases err with ei | _
    · (try wp_auto)
      iapply HΦ
      iframe HRD
      iunfold authedOutB
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
        iunfold authedOutB
        isplitr
        · iexact HaUE
        isplitr
        · ipureintro; intro h; rw [h] at Hon; cases Hon
        isplitr
        · iintro %h; cases h
        · iintro %_; iexact Hb
      · ihave #Hpb := principalBound_of_ctxBoundOrTLS s E.authMode (GoInterface.ok ctx) a user rev $$ [$Hbnd $Hau]
        iunfold authInfoIs at Hau
        icases Hau with ⟨%Hann, -, -⟩
        (try wp_auto)
        rw [_root_.decide_eq_false Hann]
        (try wp_auto)
        iapply HΦ
        iframe HRD
        iunfold authedOutB
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

end proof

end EtcdGrove
end Perennial
