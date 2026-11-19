/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthAdmin__isPermitted
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

theorem v3rpc.AuthAdmin.isPermitted.wp_proof
    (hAI : EtcdServer.AuthInfoFromCtx.spec (GF := GF) (hG := hG))
    (hAS : EtcdServer.AuthStore.spec (GF := GF) (hG := hG)) :
    v3rpc.AuthAdmin.isPermitted.spec (GF := GF) (hG := hG) := by
  intro aa s E ctx cd tok n
  wp_start as ⟨#Haa, #Hlb, #Hctx, #Hlib, #HtokC, HRD⟩
  iunfold v3rpc.authAdminIs at Haa
  icases Haa with ⟨%Hann0, #Hag, #Hau⟩
  ihave #Hnil := srvAdminNilOk_of_srvAuthAt s E $$ Hau
  iunfold srvAuthAt at Hau
  icases Hau with ⟨%st, %cca, #Has, #Hreq, #Hreqb, #Hcca, #Hast⟩
  iunfold srvAdminNilOk at Hnil
  icases Hnil with ⟨%st2, #Has2, #Hnil⟩
  icombine Has Has2 gives %Heq
  subst Heq
  iunfold apply.isAuthStore at Hast
  icases Hast with ⟨%ai, %Hai, -, -, -, #HAdm, -⟩
  iunfold adminNilOk at Hnil
  icases Hnil with ⟨%ai2, %Hai2, #HAdmNil⟩
  have Hai2' : ai = ai2 := GoInterface.ok.inj (Hai.symm.trans Hai2)
  subst Hai2'
  subst Hai
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply (hAI s (GoInterface.ok ai) E.RD E.authMode cca ctx cd n tok)
    $$ [$HRD] as %a %err ⟨HRD, Ha, #Herr0, #Hb, -, #Hz, #Hne, -⟩
  · iframe #
  ihave #Herr := authApplyErrIs_apply _ $$ Herr0
  (try wp_auto)
  rcases err with ei | _
  · (try wp_auto)
    iapply HΦ
    iframe HRD
    iunfold adminOutC
    isplitr
    · iunfold adminOutB
      iframe #
      iintro %h; cases h
    · iintro %hne
      rcases (Bool.eq_false_or_eq_true E.authMode.isOn).symm with hon | hon
      · iapply (adminWhy_off s E.authMode n _ _ hon)
      · iapply (adminWhy_of_reqSide s E.authMode n _ _)
        iunfold reqSideWhy
        ihave ⟨#Hit, #Hen', #Htk⟩ := Hne $$ %hon %hne
        iframe Hen'
        iright
        iframe Hit Htk
  · (try wp_auto)
    wp_apply (hAS s (GoInterface.ok ai))
    · iframe #
    (try wp_auto)
    iunfold authInfoOpt at Ha
    rcases (Bool.eq_false_or_eq_true E.authMode.isOn).symm with hon | hon
    · -- auth off: the store's contract; no reason to give
      icases Ha with (%Han | ⟨%user, %rev, #Hau⟩)
      · subst Han
        (try wp_auto)
        wp_apply HAdmNil $$ [$HRD] as %err2 ⟨HRD, #Herr2, %Hoff, #Hv⟩
        (try wp_auto)
        iapply HΦ
        iframe HRD
        iunfold adminOutC
        isplitr
        · iunfold adminOutB
          iframe #
          iintro %h
          subst h
          iexists none
          isplitl
          · iapply (adminRes_of_adminVerdict _ _) $$ Hv
          iintro !> -; iunfold principalBound; itrivial
        · iintro %_; iapply (adminWhy_off s E.authMode n _ _ hon)
      · ihave #Hap := authInfoIs_pointsto a user rev $$ Hau
        ihave #Hpb := principalBound_of_ctxBoundOrTLS_gate s E.authMode tok a user rev $$ [$Hb $Hau]
        iunfold authInfoIs at Hau
        icases Hau with ⟨%Hann, -, -⟩
        (try wp_auto)
        wp_apply HAdm $$ [$Hap $HRD] as %err2 ⟨-, HRD, #Herr2, %Hoff, #Hv⟩
        (try wp_auto)
        iapply HΦ
        iframe HRD
        iunfold adminOutC
        isplitr
        · iunfold adminOutB
          iframe #
          iintro %h
          subst h
          iexists (some _)
          isplitl
          · iapply (adminRes_of_adminVerdict _ _) $$ Hv
          iexact Hpb
        · iintro %_; iapply (adminWhy_off s E.authMode n _ _ hon)
    · -- auth on: the bound request side's admin check at the lower bound
      ihave #HreqB : isReqAuthBound (GoInterface.ok ai) E.RD E.authMode $$ []
      · iapply Hreqb; ipureintro; exact hon
      ihave #HAdmLb := isReqAuthBound_adminLb (GoInterface.ok ai) E.RD E.authMode ai rfl $$ HreqB
      ihave #Hz' := Hz $$ %hon
      icases Ha with (%Han | ⟨%user, %rev, #Hau⟩)
      · subst Han
        (try wp_auto)
        ihave #HAdmN := HAdmLb $$ %n %null %(none : Option go_etcd_io.etcd.server.v3.auth.AuthInfo)
          %(DfracOwn 1)
        wp_apply HAdmN $$ [$HRD] as %err2 ⟨HRD, -, #Herr2, #Hv⟩
        · iframe #; iunfold auth.authInfoAt; ipureintro; rfl
        ihave #Herr2' := authApplyErrIs_apply _ $$ Herr2
        (try wp_auto)
        iapply HΦ
        iframe HRD
        iunfold adminOutC
        isplitr
        · iunfold adminOutB
          iframe #
          iintro %h
          subst h
          iexists none
          isplitl
          · iapply (adminRes_of_verdictFromO _ _ _) $$ Hv
          iintro !> -; iunfold principalBound; itrivial
        · iintro %hne
          iapply (adminWhy_none s E.authMode n _ _ hne) $$ [] Hv
          iapply Hz'; exact ⟨rfl, rfl⟩
      · ihave #Hap := authInfoIs_pointsto a user rev $$ Hau
        ihave #Hpb := principalBound_of_ctxBoundOrTLS_gate s E.authMode tok a user rev $$ [$Hb $Hau]
        ihave #Hpb' := Hpb $$ %hon
        iunfold authInfoIs at Hau
        icases Hau with ⟨%Hann, -, -⟩
        (try wp_auto)
        ihave #HAdmS := HAdmLb $$ %n %a %(some ({ Username' := user, Revision' := rev } :
            go_etcd_io.etcd.server.v3.auth.AuthInfo)) %DfracDiscarded
        wp_apply HAdmS $$ [$HRD] as %err2 ⟨HRD, -, #Herr2, #Hv⟩
        · iframe #; iunfold auth.authInfoAt; iexact Hap
        ihave #Herr2' := authApplyErrIs_apply _ $$ Herr2
        (try wp_auto)
        iapply HΦ
        iframe HRD
        iunfold adminOutC
        isplitr
        · iunfold adminOutB
          iframe #
          iintro %h
          subst h
          iexists (some _)
          isplitl
          · iapply (adminRes_of_verdictFromO _ _ _) $$ Hv
          iexact Hpb
        · iintro %hne
          iapply (adminWhy_some s E.authMode n _ _ _ hne) $$ Hpb' Hv


end proof

end EtcdGrove
end Perennial
