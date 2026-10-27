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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.authApplierV3.UserGet.wp_proof :
    apply.authApplierV3.UserGet.spec (GF := GF) (hG := hG) := by
  intro E c inner p r log Pre Q Post info
  wp_start as ⟨#Hauth, #Hinner, ⟨⟨⟨%n, #Hr⟩, HRW⟩, #Hgate⟩, Hm, Hwt, #Hsp⟩
  iunfold apply.authIs at Hauth
  icases Hauth with ⟨#Happ, ⟨%st, #Hasf, #Hst⟩, -, -⟩
  iunfold apply.mPre at Hm
  icases Hm with ⟨Hkv, Hres, Hcs⟩
  ihave ⟨Hard, Hkv⟩ := apply.kvOwn_rd E log $$ Hkv
  ihave ⟨Hinfo, Hres⟩ := apply.chainRes_auth_out c p inner info $$ Happ Hres
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
  wp_apply HAdmin $$ [$Hinfo $Hard] as %err ⟨Hinfo, Hard, #HeI, -, #Hadm⟩
  ihave Hkv := Hkv $$ Hard
  cases err with
  | nil =>
    wp_auto
    iunfold apply.chainResAny at Hres
    icases Hres with ⟨%info', Hres⟩
    wp_apply HResp $$ %go!"UserGet" %r %log %Pre %Q %Post %info' [] [Hkv Hres Hcs Hwt HRW] as %resp %err' ⟨Hpost, #HeI'⟩
    · ipureintro; simp [apply.respMethods]
    · simp [apply.reqFacts]
      iunfold apply.mPre
      iframe
      iframe Hsp
      iframe Hgate
      iexists _; iexact Hr
    ihave #Hug : iprop(∀ _ : err' = GoInterface.nil, ∃ n : GoString,
        apply.authUserGetIs r n ∗ apply.userGetClass E.authMode info n) $$ []
    · iintro %_; iexists n; iframe Hr; iunfold apply.userGetClass; ileft; iexact Hadm
    iapply HΦ
    iframe Hug
    isplitl; rotate_left
    · first | iexact HeI' | iexact HeI | iapply applyErrIs_nil
    iunfold apply.mPost at Hpost
    iunfold apply.mPost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    iframe Hkv HPP
    iapply apply.chainResAny_auth_in c p (.ok bi) _ $$ Happ Hinfo Hres
  | ok e' =>
    wp_auto
    by_cases hn : n = info.Username'
    · simp only [hn, _root_.decide_true, Bool.not_true]
      wp_auto
      iunfold apply.chainResAny at Hres
      icases Hres with ⟨%info', Hres⟩
      wp_apply HResp $$ %go!"UserGet" %r %log %Pre %Q %Post %info' [] [Hkv Hres Hcs Hwt HRW] as %resp %err' ⟨Hpost, #HeI'⟩
      · ipureintro; simp [apply.respMethods]
      · simp [apply.reqFacts]
        iunfold apply.mPre
        iframe
        iframe Hsp
        iframe Hgate
        iexists _; iexact Hr
      ihave #Hug : iprop(∀ _ : err' = GoInterface.nil, ∃ n : GoString,
          apply.authUserGetIs r n ∗ apply.userGetClass E.authMode info n) $$ []
      · iintro %_; iexists _; iframe Hr; iunfold apply.userGetClass; iright; ipureintro
        first | exact hn | rfl
      iapply HΦ
      iframe Hug
      isplitl; rotate_left
      · first | iexact HeI' | iexact HeI | iapply applyErrIs_nil
      iunfold apply.mPost at Hpost
      iunfold apply.mPost
      icases Hpost with ⟨Hkv, Hres, HPP⟩
      iframe Hkv HPP
      iapply apply.chainResAny_auth_in c p (.ok bi) _ $$ Happ Hinfo Hres
    simp only [hn, decide_false, Bool.not_false]
    wp_auto
    wp_alloc resp as Hresp
    wp_auto
    ihave #Hug : iprop(∀ _ : GoInterface.ok e' = GoInterface.nil, ∃ n : GoString,
        apply.authUserGetIs r n ∗ apply.userGetClass E.authMode info n) $$ []
    · iintro %h; cases h
    iapply HΦ
    iframe Hug
    isplitl; rotate_left
    · first | iexact HeI' | iexact HeI | iapply applyErrIs_nil
    ihave HPre := apply.csContract_pre _ _ _ _ _ $$ Hcs
    iunfold apply.mPost
    iframe Hkv
    isplitl [Hinfo Hres]
    · iapply apply.chainResAny_auth_in c p (.ok bi) _ $$ Happ Hinfo Hres
    iright; iexact HPre

end proof

end EtcdGrove
end Perennial
