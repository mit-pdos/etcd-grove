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

theorem EtcdServer.checkMembershipOperationPermission.wp_proof
    (hAI : EtcdServer.AuthInfoFromCtx.spec (GF := GF) (hG := hG))
    (hAS : EtcdServer.AuthStore.spec (GF := GF) (hG := hG)) :
    EtcdServer.checkMembershipOperationPermission.spec (GF := GF) (hG := hG) := by
  intro s E ctx cd
  wp_start as ⟨#Hau, #Hnil, #Hctx, HRD⟩
  iunfold srvAuthAt at Hau
  icases Hau with ⟨%st, %cca, %P, %f, #Has, #Hreq, #Hcca, #Hast⟩
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
  wp_apply (hAI s (GoInterface.ok ai) E.RD cca ctx cd) $$ [$HRD] as %a %err ⟨HRD, Ha, #Herr⟩
  · iframe #
  (try wp_auto)
  rcases err with ei | _
  · (try wp_auto)
    iapply HΦ
    iframe HRD
    iunfold adminOut
    iframe #
    iintro %h; cases h
  · (try wp_auto)
    wp_apply (hAS s (GoInterface.ok ai))
    · iframe #
    (try wp_auto)
    iunfold authInfoOpt at Ha
    icases Ha with (%Han | ⟨%user, %rev, Hau⟩)
    · subst Han
      (try wp_auto)
      wp_apply HAdmNil $$ [$HRD] as %err2 ⟨HRD, #Herr2, %Hoff, #Hv⟩
      (try wp_auto)
      iapply HΦ
      iframe HRD
      iunfold adminOut
      iframe #
      iintro %h
      subst h
      iexists none
      iapply (adminRes_of_adminVerdict _ _) $$ Hv
    · ihave #Hap := authInfoIs_pointsto a user rev $$ Hau
      iunfold authInfoIs at Hau
      icases Hau with ⟨%Hann, -, -⟩
      (try wp_auto)
      wp_apply HAdm $$ [$Hap $HRD] as %err2 ⟨-, HRD, #Herr2, %Hoff, #Hv⟩
      (try wp_auto)
      iapply HΦ
      iframe HRD
      iunfold adminOut
      iframe #
      iintro %h
      subst h
      iexists (some _)
      iapply (adminRes_of_adminVerdict _ _) $$ Hv

end proof

end EtcdGrove
end Perennial
