/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.newQuotaApplierV3
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.WriteLemmas
public import Spec.go_etcd_io.etcd.server.v3.storage.NewBackendQuota
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.quotaApplierV3__Put
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.quotaApplierV3__Txn
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.quotaApplierV3__LeaseGrant
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

theorem apply.newQuotaApplierV3.wp_proof
    (hNBQ : storage.NewBackendQuota.spec (GF := GF) (hG := hG))
    (hPut : apply.quotaApplierV3.Put.spec (GF := GF) (hG := hG))
    (hTxn : apply.quotaApplierV3.Txn.spec (GF := GF) (hG := hG))
    (hLG : apply.quotaApplierV3.LeaseGrant.spec (GF := GF) (hG := hG)) :
    apply.newQuotaApplierV3.spec (GF := GF) (hG := hG) := by
  intro lg cfg be base Hbuq
  wp_start as #Hlg
  wp_auto
  wp_apply hNBQ _ _ _ _ Hbuq $$ [$Hlg] as %q #Hq
  wp_alloc p as Hp
  iStructNamed Hp
  ipersist applierV3
  ipersist q
  wp_auto
  iapply HΦ
  isplitr
  · iexists p; iframe applierV3; ipureintro; rfl
  iintro !> %E %c #Hbase
  ihave #Hb := Hbase
  iunfold apply.applierSpec at Hb
  icases Hb with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨#HPut, #HDel, #HRange, #HTxn, #HRev, #HGrant, #HResp, #HResp0, #HStatus, #HCluster,
    #HApply, #HCmp⟩
  iunfold apply.applierSpec
  iexists ⟨go.GoType.PointerType quotaApplierV3.ty, #p⟩
  isplitr
  · ipureintro; rfl
  iunfold apply.applierTriples
  isplitr
  · -- Put: the quota applier's
    imodintro
    iintro %r %rq %o %log %F %Pre %Q %Post %info
    imodintro
    iintro %Φ' ⟨Htt, Hpre, #HF⟩ HΦ'
    iapply (hPut E c (.ok bi) p r rq o log F Pre Q Post info) $$ [Hpre Htt] HΦ'
    iframe Hpre Htt
    iunfold apply.quotaIs
    iframe #
  isplitr
  · -- DeleteRange: the inner applier's (promoted)
    imodintro
    iintro %r %rq %o %log %F %Pre %Q %Post %info
    imodintro
    iintro %Φ' ⟨Htt, Hpre, #HF⟩ HΦ'
    rw [method_unfold (t := go.GoType.PointerType quotaApplierV3.ty) (m := go!"DeleteRange")]
    wp_call
    wp_auto
    iunfold apply.deletePre at Hpre
    icases Hpre with ⟨%Hk, #Hcp, #Hr, Hm⟩
    ihave #Hcp := apply.certPre_quota _ _ _ _ $$ Hcp
    icases apply.mPre_split_chain _ _ _ _ _ _ _ _ $$ Hm with ⟨Hkv, Hres⟩
    ihave Hres := apply.chainRes_quota_out c p (.ok bi) info $$ applierV3 Hres
    iapply HDel $$ %r %rq %o %log %F %Pre %Q %Post %info [Htt Hkv Hres]
    · iframe Htt
      iunfold apply.deletePre
      iframe #
      isplitr
      · ipureintro; exact Hk
      iapply apply.mPre_of_rest
      iframe
    inext
    iintro %resp %trace %err ⟨Hpost, Htrc, Htt⟩
    iapply HΦ'
    iframe Htt
    isplitr [Htrc]
    rotate_left
    · iexact Htrc
    iunfold apply.kvPostF at Hpost
    iunfold apply.kvPostF
    icases Hpost with ⟨%oc, %Hst, HR, Hkv, Hres, HPP, #Hcls, #Hlc⟩
    ihave #Hcls := apply.chainClass_quota E.authMode info c rq oc $$ Hcls
    ihave #Hlc := apply.chainLeaseClass_quota E.authMode info _ c rq oc $$ Hlc
    iexists oc
    iframe HR Hkv HPP Hcls Hlc
    isplitr
    · ipureintro
      simp only [apply.chainStep, apply.quotaChecks, Hk.2.1]
      simpa using Hst
    iapply apply.chainRes_quota_in c p (.ok bi) info $$ applierV3 Hres
  isplitr
  · -- Range: the inner applier's (promoted)
    imodintro
    iintro %r %rq %o %log %info
    imodintro
    iintro %Φ' ⟨Htt, Hpre⟩ HΦ'
    rw [method_unfold (t := go.GoType.PointerType quotaApplierV3.ty) (m := go!"Range")]
    wp_call
    wp_auto
    iunfold apply.rangePre at Hpre
    icases Hpre with ⟨%Hk, #Hr, Hkv, Hres⟩
    ihave Hres := apply.chainRes_quota_out c p (.ok bi) info $$ applierV3 Hres
    iapply HRange $$ %r %rq %o %log %info [Htt Hkv Hres]
    · iframe Htt
      iunfold apply.rangePre
      iframe
      iframe #
      ipureintro; exact Hk
    inext
    iintro %resp %trace %err ⟨Hpost, Htrc, Htt⟩
    iapply HΦ'
    iframe Htt
    isplitr [Htrc]
    rotate_left
    · iexact Htrc
    iunfold apply.rangePost at Hpost
    iunfold apply.rangePost
    icases Hpost with ⟨%oc, %Hst, HR, Hkv, Hres, #Hcls⟩
    ihave #Hcls := apply.chainClass_quota E.authMode info c rq oc $$ Hcls
    iexists oc
    iframe HR Hkv Hcls
    isplitr
    · ipureintro
      simp only [apply.chainStep, apply.quotaChecks, Hk.2.1]
      simpa using Hst
    iapply apply.chainRes_quota_in c p (.ok bi) info $$ applierV3 Hres
  isplitr
  · -- Txn: the quota applier's
    imodintro
    iintro %r %skip %rq %t %log %F %Pre %Q %Post %info
    imodintro
    iintro %Φ' ⟨Htt, Hpre, #HF⟩ HΦ'
    iapply (hTxn E c (.ok bi) p r skip rq t log F Pre Q Post info) $$ [Hpre Htt] HΦ'
    iframe Hpre Htt
    iunfold apply.quotaIs
    iframe #
  isplitr
  · -- LeaseRevoke: the inner applier's (promoted)
    imodintro
    iintro %r %rq %id %log %T %rs %Pre %Q %Post %info
    imodintro
    iintro %Φ' ⟨Htt, Hpre⟩ HΦ'
    rw [method_unfold (t := go.GoType.PointerType quotaApplierV3.ty) (m := go!"LeaseRevoke")]
    wp_call
    wp_auto
    iunfold apply.revokePre at Hpre
    icases Hpre with ⟨%Hk, #Hcp, #Hr, Hm, Hrr⟩
    ihave #Hcp := apply.certPre_quota _ _ _ _ $$ Hcp
    icases apply.mPre_split_chain _ _ _ _ _ _ _ _ $$ Hm with ⟨Hkv, Hres⟩
    ihave Hres := apply.chainRes_quota_out c p (.ok bi) info $$ applierV3 Hres
    iapply HRev $$ %r %rq %id %log %T %rs %Pre %Q %Post %info [Htt Hkv Hres Hrr]
    · iframe Htt
      iunfold apply.revokePre
      iframe # Hrr
      isplitr
      · ipureintro; exact Hk
      iapply apply.mPre_of_rest
      iframe
    inext
    iintro %resp %err ⟨Hpost, Htt⟩
    iapply HΦ'
    iframe Htt
    iunfold apply.kvPost at Hpost
    iunfold apply.kvPost
    icases Hpost with ⟨%oc, %Hst, HR, Hkv, Hres, HPP, #Hcls, #Hlc⟩
    ihave #Hcls := apply.chainClass_quota E.authMode info c rq oc $$ Hcls
    ihave #Hlc := apply.chainLeaseClass_quota E.authMode info _ c rq oc $$ Hlc
    iexists oc
    iframe HR Hkv HPP Hcls Hlc
    isplitr
    · ipureintro
      simp only [apply.chainStep, apply.quotaChecks, Hk.2.1]
      simpa using Hst
    iapply apply.chainRes_quota_in c p (.ok bi) info $$ applierV3 Hres
  isplitr
  · -- `LeaseGrant` (the lease-grant stage, 2.11): the layer's own
    imodintro
    iintro %r %rq %g %log %T %rs %U %Pre %Q %Post %info
    imodintro
    iintro %Φ' ⟨Htt, Hpre⟩ HΦ'
    iapply (hLG E c (.ok bi) p r rq g log T rs U Pre Q Post info) $$ [Hpre Htt] HΦ'
    iframe Hpre Htt
    iunfold apply.quotaIs
    iframe #
  isplitr
  · -- the methods that leave the log as it is: the inner applier's (promoted)
    imodintro
    iintro %m %r %log %Pre %Q %Post %info %hm
    imodintro
    iintro %Φ' Hpre HΦ'
    simp only [apply.respMethods, List.mem_cons, List.not_mem_nil, _root_.or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    all_goals
      rw [method_unfold (t := go.GoType.PointerType quotaApplierV3.ty)]
      wp_call
      wp_auto
      icases Hpre with ⟨Htt, HR, Hm, #Hsp⟩
      icases apply.mPreW_split_chain _ _ _ _ _ _ _ _ $$ Hm with ⟨Hkv, Hres⟩
      ihave Hres := apply.chainRes_quota_out c p (.ok bi) info $$ applierV3 Hres
      iapply HResp $$ %_ %r %log %Pre %Q %Post %info [] [Htt HR Hkv Hres]
      · ipureintro; simp [apply.respMethods]
      · iframe Htt HR
        iframe #
        iapply apply.mPreW_of_rest
        iframe
      inext
      iintro %resp %err ⟨Htt, Hpost, #HeI⟩
      iapply HΦ'
      iframe Htt
      iunfold apply.mPostW at Hpost
      icases Hpost with ⟨Hpost, Hrt⟩
      iunfold apply.mPostW
      iframe Hrt
      iunfold apply.mPost at Hpost
      iunfold apply.mPost
      icases Hpost with ⟨Hkv, Hres, HPP⟩
      iframe HeI Hkv HPP
      iapply apply.chainResAny_quota_in c p (.ok bi) $$ applierV3 Hres
  isplitr
  · -- `AuthEnable`, `AuthDisable`: the inner applier's (promoted)
    imodintro
    iintro %m %log %Pre %Q %Post %info %hm %hon
    imodintro
    iintro %Φ' Hpre HΦ'
    simp only [apply.resp0Methods, List.mem_cons, List.not_mem_nil, _root_.or_false] at hm
    rcases hm with rfl | rfl
    all_goals
      rw [method_unfold (t := go.GoType.PointerType quotaApplierV3.ty)]
      wp_call
      wp_auto
      icases Hpre with ⟨Htt, Hpre, HRW⟩
      icases apply.mPreW_split_chain _ _ _ _ _ _ _ _ $$ Hpre with ⟨Hkv, Hres⟩
      ihave Hres := apply.chainRes_quota_out c p (.ok bi) info $$ applierV3 Hres
      iapply HResp0 $$ %_ %log %Pre %Q %Post %info [] [] [Htt Hkv Hres HRW]
      · ipureintro; simp [apply.resp0Methods]
      · ipureintro; exact hon
      · iframe Htt HRW
        iapply apply.mPreW_of_rest
        iframe
      inext
      iintro %resp %err ⟨Htt, Hpost, #HeI⟩
      iapply HΦ'
      iframe Htt
      iunfold apply.mPostW at Hpost
      icases Hpost with ⟨Hpost, Hrt⟩
      iunfold apply.mPostW
      iframe Hrt
      iunfold apply.mPost at Hpost
      iunfold apply.mPost
      icases Hpost with ⟨Hkv, Hres, HPP⟩
      iframe HeI Hkv HPP
      iapply apply.chainResAny_quota_in c p (.ok bi) $$ applierV3 Hres
  isplitr
  · -- `AuthStatus`: the inner applier's (promoted)
    imodintro
    iintro %log %info
    imodintro
    iintro %Φ' ⟨Htt, Hkv, Hres⟩ HΦ'
    rw [method_unfold (t := go.GoType.PointerType quotaApplierV3.ty) (m := go!"AuthStatus")]
    wp_call
    wp_auto
    ihave Hres := apply.chainRes_quota_out c p (.ok bi) info $$ applierV3 Hres
    iapply HStatus $$ %log %info [Htt Hkv Hres]
    · iframe
    inext
    iintro %resp %err ⟨Htt, Hkv, Hres, #HeI⟩
    iapply HΦ'
    iframe Htt HeI Hkv
    iapply apply.chainRes_quota_in c p (.ok bi) info $$ applierV3 Hres
  isplitr
  · -- the cluster's methods: the inner applier's (promoted)
    imodintro
    iintro %m %r %v3 %log %Pre %Q %Post %cr %rs %info %hm
    imodintro
    iintro %Φ' Hpre HΦ'
    simp only [apply.clusterMethods, List.mem_cons, List.not_mem_nil, _root_.or_false] at hm
    rcases hm with rfl | rfl | rfl
    all_goals
      rw [method_unfold (t := go.GoType.PointerType quotaApplierV3.ty)]
      wp_call
      wp_auto
      icases Hpre with ⟨HR, Hm, HFS, HRO⟩
      icases apply.mPreV_split_chain _ _ _ _ _ _ _ _ _ $$ Hm with ⟨Hkv, Hres⟩
      ihave Hres := apply.chainRes_quota_out c p (.ok bi) info $$ applierV3 Hres
      iapply HCluster $$ %_ %r %v3 %log %Pre %Q %Post %cr %rs %info [] [HR Hkv Hres HFS HRO]
      · ipureintro; simp [apply.clusterMethods]
      · iframe HR HFS HRO
        iapply apply.mPreV_of_rest
        iframe
      inext
      iintro ⟨Hpost, HFS, HRO⟩
      iapply HΦ'
      iframe HFS HRO
      iunfold apply.mPostV at Hpost
      iunfold apply.mPostV
      icases Hpost with ⟨Hkv, Hres, HPP, Hrt⟩
      iframe Hkv HPP Hrt
      iapply apply.chainRes_quota_in c p (.ok bi) info $$ applierV3 Hres
  isplitr
  · -- `Apply`: the inner applier's (promoted), its `applyFunc` under the inner's resources
    imodintro
    iintro %r %rq %skip %v3 %af %A %B
    imodintro
    iintro %Φ' ⟨#Hw, HA, #Hlend, #Haf⟩ HΦ'
    rw [method_unfold (t := go.GoType.PointerType quotaApplierV3.ty) (m := go!"Apply")]
    wp_call
    wp_auto
    iapply HApply $$ %r %rq %skip %v3 %af %A %B [HA]
    · iframe HA
      iframe #
      imodintro
      iintro %Φ'' ⟨Hres, HA⟩ HΦ''
      ihave Hres := apply.chainRes_quota_in c p (.ok bi) (apply.principalOf rq) $$ applierV3 Hres
      iapply Haf $$ [Hres HA]
      · iframe
      inext
      iintro %ar ⟨Hres, HB⟩
      iapply HΦ''
      iframe HB
      iapply apply.chainResAny_quota_out c p (.ok bi) $$ applierV3 Hres
    inext
    iintro %ar Hpost
    iapply HΦ'
    icases Hpost with (⟨HB, #Hadm⟩ | Hrej)
    · ileft
      iframe HB
      iapply apply.adminPass_wrap E.authMode c (.quota c) rq rfl $$ Hadm
    · iright
      iexact Hrej
  · -- `Compaction`: the inner applier's (promoted)
    iunfold apply.cmpTriple
    iunfold apply.cmpTriple at HCmp
    imodintro
    iintro %cr %rev %log %crev %Pre %Q %Post %info
    imodintro
    iintro %Φ' ⟨#Hcr, %Hadm, HCp, Htt, Hm, Hc⟩ HΦ'
    rw [method_unfold (t := go.GoType.PointerType quotaApplierV3.ty) (m := go!"Compaction")]
    wp_call
    wp_auto
    icases apply.mPre_split_chain _ _ _ _ _ _ _ _ $$ Hm with ⟨Hkv, Hres⟩
    ihave Hres := apply.chainRes_quota_out c p (.ok bi) info $$ applierV3 Hres
    iapply HCmp $$ %cr %rev %log %crev %Pre %Q %Post %info [HCp Htt Hkv Hres Hc]
    · iframe HCp Htt Hc; iframe #; isplitr; · ipureintro; exact Hadm
      iapply apply.mPre_of_rest; iframe
    inext
    iintro %resp %ch %trace %err ⟨Htt, Hkv, Hres, HPP, Hc, Hans⟩
    iapply HΦ'
    iframe Htt
    rw [apply.chainCompacts_quota c, apply.cmpAnswerIs_congr (.quota c) c (apply.chainCompacts_quota c)]
    iframe Hkv HPP
    isplitr [Hc Hans]
    rotate_left
    · isplitl [Hc]
      · iexact Hc
      · iexact Hans
    iapply apply.chainRes_quota_in c p (.ok bi) info $$ applierV3 Hres

end proof

end EtcdGrove
end Perennial
