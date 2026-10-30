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

/-- One proof for both modes (the auth-mode merge, 2026-10-29: the former `wp_proof` and
(`isPermitted_bound`): the binding under the mode's gate). -/
theorem v3rpc.AuthAdmin.isPermitted.wp_proof
    (hAI : EtcdServer.AuthInfoFromCtx.spec (GF := GF) (hG := hG))
    (hAS : EtcdServer.AuthStore.spec (GF := GF) (hG := hG)) :
    v3rpc.AuthAdmin.isPermitted.spec (GF := GF) (hG := hG) := by
  intro aa s E ctx cd
  wp_start as ⟨#Haa, #Hnil, #Hctx, HRD⟩
  iunfold v3rpc.authAdminIs at Haa
  icases Haa with ⟨%Hann, #Hag, #Hau⟩
  iunfold srvAuthAt at Hau
  icases Hau with ⟨%st, %cca, %P, %f, #Has, #Hreq, #Hreqb, #Hcca, #Hast⟩
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
  wp_apply (hAI s (GoInterface.ok ai) E.RD E.authMode cca ctx cd)
    $$ [$HRD] as %a %err ⟨HRD, Ha, #Herr, #Hb⟩
  · iframe #
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
      icases Hau with ⟨%Hann', -, -⟩
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

end proof

end EtcdGrove
end Perennial
