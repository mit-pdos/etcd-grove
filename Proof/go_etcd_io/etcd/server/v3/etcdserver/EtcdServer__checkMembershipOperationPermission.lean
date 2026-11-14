/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__checkMembershipOperationPermission.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__checkMembershipOperationPermission
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AuthInfoFromCtx
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AuthStore
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
`checkMembershipOperationPermission_bound`): the binding under the mode's gate. -/
theorem EtcdServer.checkMembershipOperationPermission.wp_proof
    (hAI : EtcdServer.AuthInfoFromCtx.spec (GF := GF) (hG := hG))
    (hAS : EtcdServer.AuthStore.spec (GF := GF) (hG := hG)) :
    EtcdServer.checkMembershipOperationPermission.spec (GF := GF) (hG := hG) := by
  intro s E ctx cd
  wp_start as ⟨#Hau, #Hnil, #Hctx, #Hlib, HRD⟩
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
  (try wp_auto)
  wp_apply (hAI s (GoInterface.ok ai) E.RD E.authMode cca ctx cd)
    $$ [$HRD] as %a %err ⟨HRD, Ha, #Herr0, #Hb, -⟩
  · iframe #
  ihave #Herr := authApplyErrIs_apply _ $$ Herr0
  (try wp_auto)
  rcases err with ei | _
  · (try wp_auto)
    iapply HΦ
    iframe HRD
    iunfold adminOutB
    iframe #
    iintro %h; cases h
  · (try wp_auto)
    wp_apply (hAS s (GoInterface.ok ai))
    · iframe #
    (try wp_auto)
    iunfold authInfoOpt at Ha
    icases Ha with (%Han | ⟨%user, %rev, #Hau⟩)
    · subst Han
      (try wp_auto)
      wp_apply HAdmNil $$ [$HRD] as %err2 ⟨HRD, #Herr2, %Hoff, #Hv⟩
      (try wp_auto)
      iapply HΦ
      iframe HRD
      iunfold adminOutB
      iframe #
      iintro %h
      subst h
      iexists none
      isplitl
      · iapply (adminRes_of_adminVerdict _ _) $$ Hv
      iintro !> -; iunfold principalBound; itrivial
    · ihave #Hap := authInfoIs_pointsto a user rev $$ Hau
      ihave #Hpb := principalBound_of_ctxBoundOrTLS_gate s E.authMode (GoInterface.ok ctx) a user rev $$ [$Hb $Hau]
      iunfold authInfoIs at Hau
      icases Hau with ⟨%Hann, -, -⟩
      (try wp_auto)
      wp_apply HAdm $$ [$Hap $HRD] as %err2 ⟨-, HRD, #Herr2, %Hoff, #Hv⟩
      (try wp_auto)
      iapply HΦ
      iframe HRD
      iunfold adminOutB
      iframe #
      iintro %h
      subst h
      iexists (some _)
      isplitl
      · iapply (adminRes_of_adminVerdict _ _) $$ Hv
      iexact Hpb

/-- `specC` (auth-guard-completeness G2): `wp_proof`'s, over `AuthInfoFromCtx`'s reasons at the
lower bound (`specLb`) and, with auth on, `IsAdminPermitted`'s refusal half at it (the bound request
side's row, `isReqAuthBound`). -/
theorem EtcdServer.checkMembershipOperationPermission.wp_proofC
    (hAI : EtcdServer.AuthInfoFromCtx.specLb (GF := GF) (hG := hG))
    (hAS : EtcdServer.AuthStore.spec (GF := GF) (hG := hG)) :
    EtcdServer.checkMembershipOperationPermission.specC (GF := GF) (hG := hG) := by
  intro s E ctx cd n
  wp_start as ⟨#Hau, #Hlb, #Hctx, #Hlib, HRD⟩
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
  (try wp_auto)
  wp_apply (hAI s (GoInterface.ok ai) E.RD E.authMode cca ctx cd n)
    $$ [$HRD] as %a %err ⟨HRD, Ha, #Herr0, #Hb, -, #Hz, #Hne⟩
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
      · iapply (adminWhy_of_reqSide' s E.authMode n _ _ hon)
        iunfold reqSideWhy
        iright
        iapply Hne $$ %hon %hne
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
        ihave #Hpb := principalBound_of_ctxBoundOrTLS_gate s E.authMode (GoInterface.ok ctx) a user rev $$ [$Hb $Hau]
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
      iunfold isReqAuthBound at HreqB
      icases HreqB with ⟨%ai3, %Hai3, -, -, #HAdmLb⟩
      have Hai3' : ai3 = ai := (GoInterface.ok.inj Hai3).symm
      subst Hai3'
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
        ihave #Hpb := principalBound_of_ctxBoundOrTLS_gate s E.authMode (GoInterface.ok ctx) a user rev $$ [$Hb $Hau]
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
