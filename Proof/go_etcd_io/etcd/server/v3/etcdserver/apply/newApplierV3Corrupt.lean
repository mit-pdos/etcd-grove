/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.newApplierV3Corrupt
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.WriteLemmas
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Corrupt__Put
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Corrupt__Range
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Corrupt__DeleteRange
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Corrupt__Txn
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Corrupt__LeaseGrant
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Corrupt__LeaseRevoke
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Corrupt__Compaction
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

theorem apply.newApplierV3Corrupt.wp_proof
    (hPut : apply.applierV3Corrupt.Put.spec (GF := GF) (hG := hG))
    (hRange : apply.applierV3Corrupt.Range.spec (GF := GF) (hG := hG))
    (hDel : apply.applierV3Corrupt.DeleteRange.spec (GF := GF) (hG := hG))
    (hTxn : apply.applierV3Corrupt.Txn.spec (GF := GF) (hG := hG))
    (hLG : apply.applierV3Corrupt.LeaseGrant.spec (GF := GF) (hG := hG))
    (hRev : apply.applierV3Corrupt.LeaseRevoke.spec (GF := GF) (hG := hG))
    (hCompaction : apply.applierV3Corrupt.Compaction.spec (GF := GF) (hG := hG)) :
    apply.newApplierV3Corrupt.spec (GF := GF) (hG := hG) := by
  intro base
  wp_start
  iapply wp_fupd
  wp_auto
  irename «$r0» => Hp
  generalize «$r0_ptr» = p at *
  iStructNamed Hp
  ipersist applierV3
  imodintro
  iapply HΦ
  isplitr
  · iunfold apply.corruptIs; iexact applierV3
  iintro !> %E %c #Hbase
  ihave #Hb := Hbase
  iunfold apply.applierSpec at Hb
  icases Hb with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨#HPut, #HDel, #HRange, #HTxn, #HRev, #HResp, #HResp0, #HStatus, #HCluster,
    #HApply, -⟩
  iunfold apply.applierSpec
  iexists ⟨go.GoType.PointerType applierV3Corrupt.ty, #p⟩
  isplitr
  · ipureintro; rfl
  iunfold apply.applierTriples
  isplitr
  · -- Put: the corrupt applier's
    imodintro
    iintro %r %rq %o %log %F %Pre %Q %Post %info
    imodintro
    iintro %Φ' ⟨Htt, Hpre, #HF⟩ HΦ'
    iapply (hPut E c (.ok bi) p r rq o log F Pre Q Post info) $$ [Hpre Htt] HΦ'
    iframe Hpre Htt
    iunfold apply.corruptIs
    iframe #
  isplitr
  · -- DeleteRange: the corrupt applier's
    imodintro
    iintro %r %rq %o %log %F %Pre %Q %Post %info
    imodintro
    iintro %Φ' ⟨Htt, Hpre, #HF⟩ HΦ'
    iapply (hDel E c (.ok bi) p r rq o log F Pre Q Post info) $$ [Hpre Htt] HΦ'
    iframe Hpre Htt
    iunfold apply.corruptIs
    iframe #
  isplitr
  · -- Range: the corrupt applier's
    imodintro
    iintro %r %rq %o %log %info
    imodintro
    iintro %Φ' ⟨Htt, Hpre⟩ HΦ'
    iapply (hRange E c (.ok bi) p r rq o log info) $$ [Hpre Htt] HΦ'
    iframe Hpre Htt
    iunfold apply.corruptIs
    iframe #
  isplitr
  · -- Txn: the corrupt applier's
    imodintro
    iintro %r %skip %rq %t %log %F %Pre %Q %Post %info
    imodintro
    iintro %Φ' ⟨Htt, Hpre, #HF⟩ HΦ'
    iapply (hTxn E c (.ok bi) p r skip rq t log F Pre Q Post info) $$ [Hpre Htt] HΦ'
    iframe Hpre Htt
    iunfold apply.corruptIs
    iframe #
  isplitr
  · -- LeaseRevoke: the corrupt applier's
    imodintro
    iintro %r %rq %id %log %rs %Pre %Q %Post %info
    imodintro
    iintro %Φ' ⟨Htt, Hpre⟩ HΦ'
    iapply (hRev E c (.ok bi) p r rq id log rs Pre Q Post info) $$ [Hpre Htt]
    · iframe Hpre Htt
      iunfold apply.corruptIs
      iframe #
    inext
    iintro %resp %err ⟨Htt, H1, H2⟩
    iapply HΦ'
    iframe
  isplitr
  · -- the methods that leave the log as it is: `LeaseGrant` the corrupt applier's, the others
    -- the inner applier's (promoted)
    imodintro
    iintro %m %r %log %Pre %Q %Post %info %hm
    imodintro
    iintro %Φ' Hpre HΦ'
    simp only [apply.respMethods, List.mem_cons, List.not_mem_nil, _root_.or_false] at hm
    rcases hm with rfl | hm
    · simp only [apply.reqFacts, ↓reduceIte]
      icases Hpre with ⟨Htt, HR, Hm, -⟩
      iapply (hLG E c (.ok bi) p r log Pre Q Post info) $$ [HR Hm Htt] HΦ'
      iframe HR Hm Htt
      iunfold apply.corruptIs
      iframe #
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    all_goals
      rw [method_unfold (t := go.GoType.PointerType applierV3Corrupt.ty)]
      wp_call
      wp_auto
      icases Hpre with ⟨Htt, HR, Hm, #Hsp⟩
      icases apply.mPreW_split_chain _ _ _ _ _ _ _ _ $$ Hm with ⟨Hkv, Hres⟩
      ihave Hres := apply.chainRes_corrupt_out c p (.ok bi) info $$ applierV3 Hres
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
      iapply apply.chainResAny_corrupt_in c p (.ok bi) $$ applierV3 Hres
  isplitr
  · -- `AuthEnable`, `AuthDisable`: the inner applier's (promoted)
    imodintro
    iintro %m %log %Pre %Q %Post %info %hm %hon
    imodintro
    iintro %Φ' Hpre HΦ'
    simp only [apply.resp0Methods, List.mem_cons, List.not_mem_nil, _root_.or_false] at hm
    rcases hm with rfl | rfl
    all_goals
      rw [method_unfold (t := go.GoType.PointerType applierV3Corrupt.ty)]
      wp_call
      wp_auto
      icases Hpre with ⟨Htt, Hpre, HRW⟩
      icases apply.mPreW_split_chain _ _ _ _ _ _ _ _ $$ Hpre with ⟨Hkv, Hres⟩
      ihave Hres := apply.chainRes_corrupt_out c p (.ok bi) info $$ applierV3 Hres
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
      iapply apply.chainResAny_corrupt_in c p (.ok bi) $$ applierV3 Hres
  isplitr
  · -- `AuthStatus`: the inner applier's (promoted)
    imodintro
    iintro %log %info
    imodintro
    iintro %Φ' ⟨Htt, Hkv, Hres⟩ HΦ'
    rw [method_unfold (t := go.GoType.PointerType applierV3Corrupt.ty) (m := go!"AuthStatus")]
    wp_call
    wp_auto
    ihave Hres := apply.chainRes_corrupt_out c p (.ok bi) info $$ applierV3 Hres
    iapply HStatus $$ %log %info [Htt Hkv Hres]
    · iframe
    inext
    iintro %resp %err ⟨Htt, Hkv, Hres, #HeI⟩
    iapply HΦ'
    iframe Htt HeI Hkv
    iapply apply.chainRes_corrupt_in c p (.ok bi) info $$ applierV3 Hres
  isplitr
  · -- the cluster's methods: the inner applier's (promoted)
    imodintro
    iintro %m %r %v3 %log %Pre %Q %Post %cr %rs %info %hm
    imodintro
    iintro %Φ' Hpre HΦ'
    simp only [apply.clusterMethods, List.mem_cons, List.not_mem_nil, _root_.or_false] at hm
    rcases hm with rfl | rfl | rfl
    all_goals
      rw [method_unfold (t := go.GoType.PointerType applierV3Corrupt.ty)]
      wp_call
      wp_auto
      icases Hpre with ⟨HR, Hm, HFS, HRO⟩
      icases apply.mPreV_split_chain _ _ _ _ _ _ _ _ _ $$ Hm with ⟨Hkv, Hres⟩
      ihave Hres := apply.chainRes_corrupt_out c p (.ok bi) info $$ applierV3 Hres
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
      iapply apply.chainRes_corrupt_in c p (.ok bi) info $$ applierV3 Hres
  isplitr
  · -- `Apply`: the inner applier's (promoted), its `applyFunc` under the inner's resources
    imodintro
    iintro %r %rq %skip %v3 %af %A %B
    imodintro
    iintro %Φ' ⟨#Hw, HA, #Hlend, #Haf⟩ HΦ'
    rw [method_unfold (t := go.GoType.PointerType applierV3Corrupt.ty) (m := go!"Apply")]
    wp_call
    wp_auto
    iapply HApply $$ %r %rq %skip %v3 %af %A %B [HA]
    · iframe HA
      iframe #
      imodintro
      iintro %Φ'' ⟨Hres, HA⟩ HΦ''
      ihave Hres := apply.chainRes_corrupt_in c p (.ok bi) (apply.principalOf rq) $$ applierV3 Hres
      iapply Haf $$ [Hres HA]
      · iframe
      inext
      iintro %ar ⟨Hres, HB⟩
      iapply HΦ''
      iframe HB
      iapply apply.chainResAny_corrupt_out c p (.ok bi) $$ applierV3 Hres
    inext
    iintro %ar Hpost
    iapply HΦ'
    icases Hpost with (⟨HB, #Hadm⟩ | Hrej)
    · ileft
      iframe HB
      iapply apply.adminPass_wrap E.authMode c (.corrupt c) rq rfl $$ Hadm
    · iright
      iexact Hrej
  · -- `Compaction`: the corrupt applier's (`ErrCorrupt`, nothing done)
    iunfold apply.cmpTriple
    imodintro
    iintro %cr %rev %log %crev %Pre %Q %Post %info
    imodintro
    iintro %Φ' ⟨#Hcr, %Hadm, HCp, Htt, Hm, Hc⟩ HΦ'
    iunfold apply.compactionIs at Hcr
    icases Hcr with ⟨%Hcrn, -⟩
    iapply (hCompaction p cr) $$ []
    · iframe #
    inext
    iintro %resp %ch %trace %err ⟨%Hn, #He⟩
    iapply HΦ'
    iframe Htt
    icases apply.mPre_split_chain _ _ _ _ _ _ _ _ $$ Hm with ⟨Hkv, Hres⟩
    icases apply.mPreRest_reject _ _ _ _ _ $$ Hkv with ⟨Hkv, HPre⟩
    iframe Hkv Hres
    isplitl [HPre]
    · iright; iexact HPre
    simp only [apply.chainCompacts, Bool.false_eq_true, ↓reduceIte, apply.cmpAnswerIs]
    iframe Hc He
    ipureintro; exact Hn

end proof

end EtcdGrove
end Perennial
