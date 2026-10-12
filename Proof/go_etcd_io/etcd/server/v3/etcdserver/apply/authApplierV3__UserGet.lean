/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3__UserGet
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Packaging

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.authApplierV3.UserGet.wp_proof :
    apply.authApplierV3.UserGet.spec (GF := GF) (hG := hG) := by
  intro E c inner p r log Pre Q Post
  wp_start as ⟨#Hauth, #Hinner, ⟨%n, #Hr⟩, Hm⟩
  iunfold apply.authIs at Hauth
  icases Hauth with ⟨#Happ, ⟨%st, #Hasf, #Hst⟩, -, -⟩
  iunfold apply.mPre at Hm
  icases Hm with ⟨Hkv, Hres, Hcs⟩
  ihave ⟨Hinfo, Hres⟩ := apply.chainRes_auth_out c p inner $$ Happ Hres
  iunfold apply.authInfoOwn at Hinfo
  icases Hinfo with ⟨%info, Hinfo⟩
  ihave #Hst' := Hst
  iunfold apply.isAuthStore at Hst'
  icases Hst' with ⟨%sti, %Hsti, -, -, -, #HAdmin, -⟩
  subst Hsti
  ihave #Hr' := Hr
  iunfold apply.authUserGetIs at Hr'
  icases Hr' with ⟨%Hrn, #HN⟩
  ihave #Hin := Hinner
  iunfold apply.applierSpec at Hin
  icases Hin with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨-, -, -, -, -, #HResp, -⟩
  wp_auto
  wp_apply HAdmin $$ [$Hinfo] as %err ⟨Hinfo, #HeI⟩
  cases err with
  | nil =>
    wp_auto
    wp_apply HResp $$ %go!"UserGet" %r %log %Pre %Q %Post [] [Hkv Hres Hcs] as %resp %err' ⟨Hpost, #HeI'⟩
    · ipureintro; simp [apply.respMethods]
    · simp [apply.reqFacts]
      iunfold apply.mPre
      iframe
      iexists _; iexact Hr
    iapply HΦ
    isplitl; rotate_left
    · first | iexact HeI' | iexact HeI | iapply applyErrIs_nil
    iunfold apply.mPost at Hpost
    iunfold apply.mPost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    iframe Hkv HPP
    iapply apply.chainRes_auth_in c p (.ok bi) $$ Happ [Hinfo] Hres
    iunfold apply.authInfoOwn; iexists _; iexact Hinfo
  | ok e' =>
    wp_auto
    by_cases hn : n = info.Username'
    · simp only [hn, decide_true, Bool.not_true]
      wp_auto
      wp_apply HResp $$ %go!"UserGet" %r %log %Pre %Q %Post [] [Hkv Hres Hcs] as %resp %err' ⟨Hpost, #HeI'⟩
      · ipureintro; simp [apply.respMethods]
      · simp [apply.reqFacts]
        iunfold apply.mPre
        iframe
        iexists _; iexact Hr
      iapply HΦ
      isplitl; rotate_left
      · first | iexact HeI' | iexact HeI | iapply applyErrIs_nil
      iunfold apply.mPost at Hpost
      iunfold apply.mPost
      icases Hpost with ⟨Hkv, Hres, HPP⟩
      iframe Hkv HPP
      iapply apply.chainRes_auth_in c p (.ok bi) $$ Happ [Hinfo] Hres
      iunfold apply.authInfoOwn; iexists _; iexact Hinfo
    simp only [hn, decide_false, Bool.not_false]
    wp_auto
    wp_alloc resp as Hresp
    wp_auto
    iapply HΦ
    isplitl; rotate_left
    · first | iexact HeI' | iexact HeI | iapply applyErrIs_nil
    ihave HPre := apply.csContract_pre _ _ _ _ _ $$ Hcs
    iunfold apply.mPost
    iframe Hkv
    isplitl [Hinfo Hres]
    · iapply apply.chainRes_auth_in c p (.ok bi) $$ Happ [Hinfo] Hres
      iunfold apply.authInfoOwn; iexists _; iexact Hinfo
    iright; iexact HPre

end proof

end EtcdGrove
end Perennial
