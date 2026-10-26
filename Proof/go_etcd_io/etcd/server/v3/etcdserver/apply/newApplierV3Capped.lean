/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.newApplierV3Capped
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Capped__Put
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Capped__Txn
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Capped__LeaseGrant
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

theorem apply.newApplierV3Capped.wp_proof
    (hPut : apply.applierV3Capped.Put.spec (GF := GF) (hG := hG))
    (hTxn : apply.applierV3Capped.Txn.spec (GF := GF) (hG := hG))
    (hLG : apply.applierV3Capped.LeaseGrant.spec (GF := GF) (hG := hG)) :
    apply.newApplierV3Capped.spec (GF := GF) (hG := hG) := by
  intro base
  wp_start
  wp_auto
  wp_alloc p as Hp
  iStructNamed Hp
  ipersist applierV3
  wp_auto
  iapply HΦ
  isplitr
  · iexists p; isplitr
    · ipureintro; rfl
    iunfold apply.cappedIs; iexact applierV3
  iintro !> %E %c #Hbase
  ihave #Hb := Hbase
  iunfold apply.applierSpec at Hb
  icases Hb with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨#HPut, #HDel, #HRange, #HTxn, #HRev, #HResp, #HResp0, #HStatus, #HCluster,
    #HApply⟩
  iunfold apply.applierSpec
  iexists ⟨go.GoType.PointerType applierV3Capped.ty, #p⟩
  isplitr
  · ipureintro; rfl
  iunfold apply.applierTriples
  isplitr
  · -- Put: the capped applier's
    imodintro
    iintro %r %rq %o %log %F %Pre %Q %Post %info
    imodintro
    iintro %Φ' ⟨Hpre, #HF⟩ HΦ'
    iapply (hPut E c (.ok bi) p r rq o log F Pre Q Post info) $$ [Hpre] HΦ'
    iframe Hpre
    iunfold apply.cappedIs
    iframe #
  isplitr
  · -- DeleteRange: the inner applier's (promoted)
    imodintro
    iintro %r %rq %o %log %F %Pre %Q %Post %info
    imodintro
    iintro %Φ' ⟨Hpre, #HF⟩ HΦ'
    rw [method_unfold (t := go.GoType.PointerType applierV3Capped.ty) (m := go!"DeleteRange")]
    wp_call
    wp_auto
    iunfold apply.deletePre at Hpre
    icases Hpre with ⟨%Hk, #Hcp, #Hr, Hwt, Hm⟩
    ihave #Hcp := apply.certPre_capped _ _ _ _ (by rw [Hk.2.1]; rfl) $$ Hcp
    iunfold apply.mPre at Hm
    icases Hm with ⟨Hkv, Hres, Hcs⟩
    ihave Hres := apply.chainRes_capped_out c p (.ok bi) info $$ applierV3 Hres
    iapply HDel $$ %r %rq %o %log %F %Pre %Q %Post %info [Hwt Hkv Hres Hcs]
    · iunfold apply.deletePre
      iunfold apply.mPre
      iframe
      iframe #
      ipureintro; exact Hk
    inext
    iintro %resp %trace %err ⟨Hpost, Htrc⟩
    iapply HΦ'
    isplitr [Htrc]
    rotate_left
    · iexact Htrc
    iunfold apply.kvPostF at Hpost
    iunfold apply.kvPostF
    icases Hpost with ⟨%oc, %Hst, HR, Hkv, Hres, HPP, #Hcls⟩
    ihave #Hcls := apply.chainClass_capped E.authMode info c rq oc $$ Hcls
    iexists oc
    iframe HR Hkv HPP Hcls
    isplitr
    · ipureintro
      simp only [apply.chainStep, apply.cappedRejects, Hk.2.1]
      simpa using Hst
    iapply apply.chainRes_capped_in c p (.ok bi) info $$ applierV3 Hres
  isplitr
  · -- Range: the inner applier's (promoted)
    imodintro
    iintro %r %rq %o %log %info
    imodintro
    iintro %Φ' Hpre HΦ'
    rw [method_unfold (t := go.GoType.PointerType applierV3Capped.ty) (m := go!"Range")]
    wp_call
    wp_auto
    iunfold apply.rangePre at Hpre
    icases Hpre with ⟨%Hk, #Hr, Hkv, Hres⟩
    ihave Hres := apply.chainRes_capped_out c p (.ok bi) info $$ applierV3 Hres
    iapply HRange $$ %r %rq %o %log %info [Hkv Hres]
    · iunfold apply.rangePre
      iframe
      iframe #
      ipureintro; exact Hk
    inext
    iintro %resp %trace %err ⟨Hpost, Htrc⟩
    iapply HΦ'
    isplitr [Htrc]
    rotate_left
    · iexact Htrc
    iunfold apply.rangePost at Hpost
    iunfold apply.rangePost
    icases Hpost with ⟨%oc, %Hst, HR, Hkv, Hres, #Hcls⟩
    ihave #Hcls := apply.chainClass_capped E.authMode info c rq oc $$ Hcls
    iexists oc
    iframe HR Hkv Hcls
    isplitr
    · ipureintro
      simp only [apply.chainStep, apply.cappedRejects, Hk.2.1]
      simpa using Hst
    iapply apply.chainRes_capped_in c p (.ok bi) info $$ applierV3 Hres
  isplitr
  · -- Txn: the capped applier's
    imodintro
    iintro %r %skip %rq %t %log %F %Pre %Q %Post %info
    imodintro
    iintro %Φ' ⟨Hpre, #HF⟩ HΦ'
    iapply (hTxn E c (.ok bi) p r skip rq t log F Pre Q Post info) $$ [Hpre] HΦ'
    iframe Hpre
    iunfold apply.cappedIs
    iframe #
  isplitr
  · -- LeaseRevoke: the inner applier's (promoted)
    imodintro
    iintro %r %rq %id %log %Pre %Q %Post %info
    imodintro
    iintro %Φ' Hpre HΦ'
    rw [method_unfold (t := go.GoType.PointerType applierV3Capped.ty) (m := go!"LeaseRevoke")]
    wp_call
    wp_auto
    iunfold apply.revokePre at Hpre
    icases Hpre with ⟨%Hk, #Hcp, #Hr, Hwt, Hm⟩
    -- D14h: no lease revocation in the workload
    have hF := Hk.2.2
    simp only [apply.rqOk, Hk.2.1] at hF
  isplitr
  · -- the methods that leave the log as it is: `LeaseGrant` the capped applier's, the others
    -- the inner applier's (promoted)
    imodintro
    iintro %m %r %log %Pre %Q %Post %info %hm
    imodintro
    iintro %Φ' Hpre HΦ'
    simp only [apply.respMethods, List.mem_cons, List.not_mem_nil, _root_.or_false] at hm
    rcases hm with rfl | hm
    · simp only [apply.reqFacts, ↓reduceIte]
      icases Hpre with ⟨HR, Hm, Hwt, -⟩
      iapply (hLG E c (.ok bi) p r log Pre Q Post info) $$ [HR Hm Hwt] HΦ'
      iframe HR Hm Hwt
      iunfold apply.cappedIs
      iframe #
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    all_goals
      rw [method_unfold (t := go.GoType.PointerType applierV3Capped.ty)]
      wp_call
      wp_auto
      icases Hpre with ⟨HR, Hm, Hwt, #Hsp⟩
      iunfold apply.mPre at Hm
      icases Hm with ⟨Hkv, Hres, Hcs⟩
      ihave Hres := apply.chainRes_capped_out c p (.ok bi) info $$ applierV3 Hres
      iapply HResp $$ %_ %r %log %Pre %Q %Post %info [] [HR Hkv Hres Hcs Hwt]
      · ipureintro; simp [apply.respMethods]
      · iframe HR
        iunfold apply.mPre
        iframe
        iframe #
      inext
      iintro %resp %err ⟨Hpost, #HeI⟩
      iapply HΦ'
      iunfold apply.mPost at Hpost
      iunfold apply.mPost
      icases Hpost with ⟨Hkv, Hres, HPP⟩
      iframe HeI Hkv HPP
      iapply apply.chainResAny_capped_in c p (.ok bi) $$ applierV3 Hres
  isplitr
  · -- `AuthEnable`, `AuthDisable`: the inner applier's (promoted)
    imodintro
    iintro %m %log %Pre %Q %Post %info %hm %hon
    imodintro
    iintro %Φ' Hpre HΦ'
    simp only [apply.resp0Methods, List.mem_cons, List.not_mem_nil, _root_.or_false] at hm
    rcases hm with rfl | rfl
    all_goals
      rw [method_unfold (t := go.GoType.PointerType applierV3Capped.ty)]
      wp_call
      wp_auto
      icases Hpre with ⟨Hpre, Hwt, HRW⟩
      iunfold apply.mPre at Hpre
      icases Hpre with ⟨Hkv, Hres, Hcs⟩
      ihave Hres := apply.chainRes_capped_out c p (.ok bi) info $$ applierV3 Hres
      iapply HResp0 $$ %_ %log %Pre %Q %Post %info [] [] [Hkv Hres Hcs Hwt HRW]
      · ipureintro; simp [apply.resp0Methods]
      · ipureintro; exact hon
      · iunfold apply.mPre
        iframe
      inext
      iintro %resp %err ⟨Hpost, #HeI⟩
      iapply HΦ'
      iunfold apply.mPost at Hpost
      iunfold apply.mPost
      icases Hpost with ⟨Hkv, Hres, HPP⟩
      iframe HeI Hkv HPP
      iapply apply.chainResAny_capped_in c p (.ok bi) $$ applierV3 Hres
  isplitr
  · -- `AuthStatus`: the inner applier's (promoted)
    imodintro
    iintro %log %info
    imodintro
    iintro %Φ' ⟨Hkv, Hres⟩ HΦ'
    rw [method_unfold (t := go.GoType.PointerType applierV3Capped.ty) (m := go!"AuthStatus")]
    wp_call
    wp_auto
    ihave Hres := apply.chainRes_capped_out c p (.ok bi) info $$ applierV3 Hres
    iapply HStatus $$ %log %info [Hkv Hres]
    · iframe
    inext
    iintro %resp %err ⟨Hkv, Hres, #HeI⟩
    iapply HΦ'
    iframe HeI Hkv
    iapply apply.chainRes_capped_in c p (.ok bi) info $$ applierV3 Hres
  isplitr
  · -- the cluster's methods: the inner applier's (promoted)
    imodintro
    iintro %m %r %v3 %log %Pre %Q %Post %cr %rs %info %hm
    imodintro
    iintro %Φ' Hpre HΦ'
    simp only [apply.clusterMethods, List.mem_cons, List.not_mem_nil, _root_.or_false] at hm
    rcases hm with rfl | rfl | rfl
    all_goals
      rw [method_unfold (t := go.GoType.PointerType applierV3Capped.ty)]
      wp_call
      wp_auto
      icases Hpre with ⟨HR, Hm, Hwt, HFS, HRO⟩
      iunfold apply.mPreV at Hm
      icases Hm with ⟨Hkv, Hres, Hcs⟩
      ihave Hres := apply.chainRes_capped_out c p (.ok bi) info $$ applierV3 Hres
      iapply HCluster $$ %_ %r %v3 %log %Pre %Q %Post %cr %rs %info [] [HR Hkv Hres Hcs Hwt HFS HRO]
      · ipureintro; simp [apply.clusterMethods]
      · iframe HR
        iunfold apply.mPreV
        iframe
      inext
      iintro ⟨Hpost, HFS, HRO⟩
      iapply HΦ'
      iframe HFS HRO
      iunfold apply.mPostV at Hpost
      iunfold apply.mPostV
      icases Hpost with ⟨Hkv, Hres, HPP⟩
      iframe Hkv HPP
      iapply apply.chainRes_capped_in c p (.ok bi) info $$ applierV3 Hres
  · -- `Apply`: the inner applier's (promoted), its `applyFunc` under the inner's resources
    imodintro
    iintro %r %rq %skip %v3 %af %A %B
    imodintro
    iintro %Φ' ⟨#Hw, HA, #Haf⟩ HΦ'
    rw [method_unfold (t := go.GoType.PointerType applierV3Capped.ty) (m := go!"Apply")]
    wp_call
    wp_auto
    iapply HApply $$ %r %rq %skip %v3 %af %A %B [HA]
    · iframe HA
      iframe #
      imodintro
      iintro %Φ'' ⟨Hres, HA⟩ HΦ''
      ihave Hres := apply.chainRes_capped_in c p (.ok bi) (apply.principalOf rq) $$ applierV3 Hres
      iapply Haf $$ [Hres HA]
      · iframe
      inext
      iintro %ar ⟨Hres, HB⟩
      iapply HΦ''
      iframe HB
      iapply apply.chainResAny_capped_out c p (.ok bi) $$ applierV3 Hres
    inext
    iintro %ar Hpost
    iapply HΦ'
    icases Hpost with (⟨HB, #Hadm⟩ | Hrej)
    · ileft
      iframe HB
      iapply apply.adminPass_wrap E.authMode c (.capped c) rq rfl $$ Hadm
    · iright
      iexact Hrej


end proof

end EtcdGrove
end Perennial
