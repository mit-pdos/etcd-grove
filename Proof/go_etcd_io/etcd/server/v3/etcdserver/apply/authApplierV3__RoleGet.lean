/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3__RoleGet
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.WriteLemmas
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.authApplierV3.RoleGet.wp_proof :
    apply.authApplierV3.RoleGet.spec (GF := GF) (hG := hG) := by
  intro E c inner p r log Pre Q Post info
  wp_start as ⟨#Hauth, #Hinner, ⟨⟨⟨%n, #Hr⟩, HRW⟩, #Hgate⟩, Htt, Hm, #Hsp⟩
  iunfold apply.authIs at Hauth
  icases Hauth with ⟨#Happ, ⟨%st, #Hasf, #Hst⟩, -, -⟩
  icases apply.mPreW_split_chain _ _ _ _ _ _ _ _ $$ Hm with ⟨Hkv, Hres⟩
  ihave ⟨Hard, Hkv⟩ := apply.mPreWRest_rd E log Pre Q Post $$ Hkv
  ihave ⟨Hinfo, Hres⟩ := apply.chainRes_auth_out c p inner info $$ Happ Hres
  ihave #Hst' := Hst
  iunfold apply.isAuthStore at Hst'
  icases Hst' with ⟨%sti, %Hsti, -, -, -, #HAdmin, #HHas, -⟩
  subst Hsti
  ihave #Hr' := Hr
  iunfold apply.authRoleGetIs at Hr'
  icases Hr' with ⟨%Hrn, #HN⟩
  ihave #Hin := Hinner
  iunfold apply.applierSpec at Hin
  icases Hin with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨-, -, -, -, -, #HResp, -⟩
  wp_auto
  wp_apply HAdmin $$ [$Hinfo $Hard] as %err ⟨Hinfo, Hard, #HeI, -⟩
  ihave Hkv := Hkv $$ Hard
  cases err with
  | nil =>
    wp_auto
    iunfold apply.chainResAny at Hres
    icases Hres with ⟨%info', Hres⟩
    ihave Hkv : apply.mPreW E c (.ok bi) info' log Pre Q Post $$ [Hkv Hres]
    · iapply apply.mPreW_of_rest; iframe
    wp_apply HResp $$ %go!"RoleGet" %r %log %Pre %Q %Post %info' [] [Htt Hkv HRW] as %resp %err' ⟨Htt, Hpost, #HeI'⟩
    · ipureintro; simp [apply.respMethods]
    · simp [apply.reqFacts]
      iframe
      iframe Hsp
      iframe Hgate
      iexists _; iexact Hr
    iapply HΦ
    iframe Htt
    isplitl; rotate_left
    · first | iexact HeI' | iexact HeI | iapply applyErrIs_nil
    iunfold apply.mPostW at Hpost
    icases Hpost with ⟨Hpost, Hrt⟩
    iunfold apply.mPost at Hpost
    iunfold apply.mPostW
    iframe Hrt
    iunfold apply.mPost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    iframe Hkv HPP
    iapply apply.chainResAny_auth_in c p (.ok bi) _ $$ Happ Hinfo Hres
  | ok e' =>
    wp_auto
    wp_apply HHas as %b -
    · iexact Hgate
    cases b
    · wp_auto
      irename «$r0» => Hresp
      generalize «$r0_ptr» = resp at *
      iapply HΦ
      iframe Htt
      isplitl; rotate_left
      · first | iexact HeI' | iexact HeI | iapply applyErrIs_nil
      icases apply.mPreWRest_reject _ _ _ _ _ $$ Hkv with ⟨Hkv, HPre, Hrt⟩
      iunfold apply.mPostW
      iframe Hrt
      iunfold apply.mPost
      iframe Hkv
      isplitl [Hinfo Hres]
      · iapply apply.chainResAny_auth_in c p (.ok bi) _ $$ Happ Hinfo Hres
      iright; iexact HPre
    wp_auto
    iunfold apply.chainResAny at Hres
    icases Hres with ⟨%info', Hres⟩
    ihave Hkv : apply.mPreW E c (.ok bi) info' log Pre Q Post $$ [Hkv Hres]
    · iapply apply.mPreW_of_rest; iframe
    wp_apply HResp $$ %go!"RoleGet" %r %log %Pre %Q %Post %info' [] [Htt Hkv HRW] as %resp %err' ⟨Htt, Hpost, #HeI'⟩
    · ipureintro; simp [apply.respMethods]
    · simp [apply.reqFacts]
      iframe
      iframe Hsp
      iframe Hgate
      iexists _; iexact Hr
    iapply HΦ
    iframe Htt
    isplitl; rotate_left
    · first | iexact HeI' | iexact HeI | iapply applyErrIs_nil
    iunfold apply.mPostW at Hpost
    icases Hpost with ⟨Hpost, Hrt⟩
    iunfold apply.mPost at Hpost
    iunfold apply.mPostW
    iframe Hrt
    iunfold apply.mPost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    iframe Hkv HPP
    iapply apply.chainResAny_auth_in c p (.ok bi) _ $$ Happ Hinfo Hres

end proof

end EtcdGrove
end Perennial
