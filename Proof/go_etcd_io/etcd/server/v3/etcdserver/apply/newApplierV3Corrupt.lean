/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.newApplierV3Corrupt
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Corrupt__Put
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Corrupt__Range
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Corrupt__DeleteRange
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Corrupt__Txn
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Corrupt__LeaseGrant
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Corrupt__LeaseRevoke
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

theorem apply.newApplierV3Corrupt.wp_proof
    (hPut : apply.applierV3Corrupt.Put.spec (GF := GF) (hG := hG))
    (hRange : apply.applierV3Corrupt.Range.spec (GF := GF) (hG := hG))
    (hDel : apply.applierV3Corrupt.DeleteRange.spec (GF := GF) (hG := hG))
    (hTxn : apply.applierV3Corrupt.Txn.spec (GF := GF) (hG := hG))
    (hLG : apply.applierV3Corrupt.LeaseGrant.spec (GF := GF) (hG := hG))
    (hRev : apply.applierV3Corrupt.LeaseRevoke.spec (GF := GF) (hG := hG)) :
    apply.newApplierV3Corrupt.spec (GF := GF) (hG := hG) := by
  intro E c base
  wp_start as #Hbase
  ihave #Hb := Hbase
  iunfold apply.applierSpec at Hb
  icases Hb with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨#HPut, #HDel, #HRange, #HTxn, #HRev, #HResp, #HResp0, #HStatus, #HCluster,
    #HApply⟩
  wp_auto
  wp_alloc p as Hp
  iStructNamed Hp
  ipersist applierV3
  wp_auto
  iapply HΦ
  iunfold apply.applierSpec
  iexists ⟨go.GoType.PointerType applierV3Corrupt.ty, #p⟩
  isplitr
  · ipureintro; rfl
  iunfold apply.applierTriples
  isplitr
  · -- Put: the corrupt applier's
    imodintro
    iintro %r %rq %o %log %Pre %Q %Post
    imodintro
    iintro %Φ' Hpre HΦ'
    iapply (hPut E c (.ok bi) p r rq o log Pre Q Post) $$ [Hpre] HΦ'
    iframe Hpre
    iunfold apply.corruptIs
    iframe #
  isplitr
  · -- DeleteRange: the corrupt applier's
    imodintro
    iintro %r %rq %o %log %Pre %Q %Post
    imodintro
    iintro %Φ' Hpre HΦ'
    iapply (hDel E c (.ok bi) p r rq o log Pre Q Post) $$ [Hpre] HΦ'
    iframe Hpre
    iunfold apply.corruptIs
    iframe #
  isplitr
  · -- Range: the corrupt applier's
    imodintro
    iintro %r %rq %o %log
    imodintro
    iintro %Φ' Hpre HΦ'
    iapply (hRange E c (.ok bi) p r rq o log) $$ [Hpre] HΦ'
    iframe Hpre
    iunfold apply.corruptIs
    iframe #
  isplitr
  · -- Txn: the corrupt applier's
    imodintro
    iintro %r %skip %rq %t %log %Pre %Q %Post
    imodintro
    iintro %Φ' Hpre HΦ'
    iapply (hTxn E c (.ok bi) p r skip rq t log Pre Q Post) $$ [Hpre] HΦ'
    iframe Hpre
    iunfold apply.corruptIs
    iframe #
  isplitr
  · -- LeaseRevoke: the corrupt applier's
    imodintro
    iintro %r %rq %id %log %Pre %Q %Post
    imodintro
    iintro %Φ' Hpre HΦ'
    iapply (hRev E c (.ok bi) p r rq id log Pre Q Post) $$ [Hpre] HΦ'
    iframe Hpre
    iunfold apply.corruptIs
    iframe #
  isplitr
  · -- the methods that leave the log as it is: `LeaseGrant` the corrupt applier's, the others
    -- the inner applier's (promoted)
    imodintro
    iintro %m %r %log %Pre %Q %Post %hm
    imodintro
    iintro %Φ' Hpre HΦ'
    simp only [apply.respMethods, List.mem_cons, List.not_mem_nil, _root_.or_false] at hm
    rcases hm with rfl | hm
    · simp only [apply.reqFacts, ↓reduceIte]
      iapply (hLG E c (.ok bi) p r log Pre Q Post) $$ [Hpre] HΦ'
      iframe Hpre
      iunfold apply.corruptIs
      iframe #
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    all_goals
      rw [method_unfold (t := go.GoType.PointerType applierV3Corrupt.ty)]
      wp_call
      wp_auto
      icases Hpre with ⟨HR, Hm⟩
      iunfold apply.mPre at Hm
      icases Hm with ⟨Hkv, Hres, Hcs⟩
      ihave Hres := apply.chainRes_corrupt_out c p (.ok bi) $$ applierV3 Hres
      iapply HResp $$ %_ %r %log %Pre %Q %Post [] [HR Hkv Hres Hcs]
      · ipureintro; simp [apply.respMethods]
      · iframe HR
        iunfold apply.mPre
        iframe
      inext
      iintro %resp %err ⟨Hpost, #HeI⟩
      iapply HΦ'
      iunfold apply.mPost at Hpost
      iunfold apply.mPost
      icases Hpost with ⟨Hkv, Hres, HPP⟩
      iframe HeI Hkv HPP
      iapply apply.chainRes_corrupt_in c p (.ok bi) $$ applierV3 Hres
  isplitr
  · -- `AuthEnable`, `AuthDisable`: the inner applier's (promoted)
    imodintro
    iintro %m %log %Pre %Q %Post %hm
    imodintro
    iintro %Φ' Hpre HΦ'
    simp only [apply.resp0Methods, List.mem_cons, List.not_mem_nil, _root_.or_false] at hm
    rcases hm with rfl | rfl
    all_goals
      rw [method_unfold (t := go.GoType.PointerType applierV3Corrupt.ty)]
      wp_call
      wp_auto
      iunfold apply.mPre at Hpre
      icases Hpre with ⟨Hkv, Hres, Hcs⟩
      ihave Hres := apply.chainRes_corrupt_out c p (.ok bi) $$ applierV3 Hres
      iapply HResp0 $$ %_ %log %Pre %Q %Post [] [Hkv Hres Hcs]
      · ipureintro; simp [apply.resp0Methods]
      · iunfold apply.mPre
        iframe
      inext
      iintro %resp %err ⟨Hpost, #HeI⟩
      iapply HΦ'
      iunfold apply.mPost at Hpost
      iunfold apply.mPost
      icases Hpost with ⟨Hkv, Hres, HPP⟩
      iframe HeI Hkv HPP
      iapply apply.chainRes_corrupt_in c p (.ok bi) $$ applierV3 Hres
  isplitr
  · -- `AuthStatus`: the inner applier's (promoted)
    imodintro
    iintro %log
    imodintro
    iintro %Φ' ⟨Hkv, Hres⟩ HΦ'
    rw [method_unfold (t := go.GoType.PointerType applierV3Corrupt.ty) (m := go!"AuthStatus")]
    wp_call
    wp_auto
    ihave Hres := apply.chainRes_corrupt_out c p (.ok bi) $$ applierV3 Hres
    iapply HStatus $$ %log [Hkv Hres]
    · iframe
    inext
    iintro %resp %err ⟨Hkv, Hres, #HeI⟩
    iapply HΦ'
    iframe HeI Hkv
    iapply apply.chainRes_corrupt_in c p (.ok bi) $$ applierV3 Hres
  isplitr
  · -- the cluster's methods: the inner applier's (promoted)
    imodintro
    iintro %m %r %v3 %log %Pre %Q %Post %hm
    imodintro
    iintro %Φ' Hpre HΦ'
    simp only [apply.clusterMethods, List.mem_cons, List.not_mem_nil, _root_.or_false] at hm
    rcases hm with rfl | rfl | rfl
    all_goals
      rw [method_unfold (t := go.GoType.PointerType applierV3Corrupt.ty)]
      wp_call
      wp_auto
      icases Hpre with ⟨HR, Hm⟩
      iunfold apply.mPreV at Hm
      icases Hm with ⟨Hkv, Hres, Hcs⟩
      ihave Hres := apply.chainRes_corrupt_out c p (.ok bi) $$ applierV3 Hres
      iapply HCluster $$ %_ %r %v3 %log %Pre %Q %Post [] [HR Hkv Hres Hcs]
      · ipureintro; simp [apply.clusterMethods]
      · iframe HR
        iunfold apply.mPreV
        iframe
      inext
      iintro Hpost
      iapply HΦ'
      iunfold apply.mPostV at Hpost
      iunfold apply.mPostV
      icases Hpost with ⟨Hkv, Hres, HPP⟩
      iframe Hkv HPP
      iapply apply.chainRes_corrupt_in c p (.ok bi) $$ applierV3 Hres
  · -- `Apply`: the inner applier's (promoted), its `applyFunc` under the inner's resources
    imodintro
    iintro %r %rq %skip %v3 %af %A %B
    imodintro
    iintro %Φ' ⟨#Hw, HA, #Haf⟩ HΦ'
    rw [method_unfold (t := go.GoType.PointerType applierV3Corrupt.ty) (m := go!"Apply")]
    wp_call
    wp_auto
    iapply HApply $$ %r %rq %skip %v3 %af %A %B [HA]
    · iframe HA
      iframe #
      imodintro
      iintro %Φ'' ⟨Hres, HA⟩ HΦ''
      ihave Hres := apply.chainRes_corrupt_in c p (.ok bi) $$ applierV3 Hres
      iapply Haf $$ [Hres HA]
      · iframe
      inext
      iintro %ar ⟨Hres, HB⟩
      iapply HΦ''
      iframe HB
      iapply apply.chainRes_corrupt_out c p (.ok bi) $$ applierV3 Hres
    inext
    iexact HΦ'


end proof

end EtcdGrove
end Perennial
