/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.newAuthApplierV3
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3__Apply
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3__Put
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3__Range
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3__DeleteRange
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3__Txn
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3__LeaseRevoke
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3__UserGet
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3__RoleGet
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

theorem apply.newAuthApplierV3.wp_proof
    (hApply : apply.authApplierV3.Apply.spec (GF := GF) (hG := hG))
    (hPut : apply.authApplierV3.Put.spec (GF := GF) (hG := hG))
    (hRange : apply.authApplierV3.Range.spec (GF := GF) (hG := hG))
    (hDel : apply.authApplierV3.DeleteRange.spec (GF := GF) (hG := hG))
    (hTxn : apply.authApplierV3.Txn.spec (GF := GF) (hG := hG))
    (hRev : apply.authApplierV3.LeaseRevoke.spec (GF := GF) (hG := hG))
    (hUG : apply.authApplierV3.UserGet.spec (GF := GF) (hG := hG))
    (hRG : apply.authApplierV3.RoleGet.spec (GF := GF) (hG := hG)) :
    apply.newAuthApplierV3.spec (GF := GF) (hG := hG) := by
  intro st base le RD
  wp_start as Hard
  wp_auto
  wp_alloc p as Hp
  iStructNamed Hp
  ipersist applierV3
  ipersist as'
  ipersist lessor
  imod sync.init_Mutex iprop(apply.authInfoIdle (GF := GF) p ∗ RD) ⊤
      (structFieldRef authApplierV3 go!"mu" p) $$ [mu] [authInfo Hard] with #Hmu
  · iexact mu
  · inext; iframe Hard; iunfold apply.authInfoIdle
    first | iexact authInfo | (iExactEq authInfo; rfl)
  wp_auto
  iapply HΦ
  iframe applierV3
  iintro !> %E %c %hRD #Hst #Hle #Hbase
  ihave #Hb := Hbase
  iunfold apply.applierSpec at Hb
  icases Hb with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨#HPut, #HDel, #HRange, #HTxn, #HRev, #HResp, #HResp0, #HStatus, #HCluster,
    #HApply⟩
  ihave #Hauth : apply.authIs E p (.ok bi) $$ []
  · iunfold apply.authIs
    rw [hRD]
    iframe applierV3 Hmu
    isplitl
    · iexists st; iframe #
    · iexists le; iframe #
  iunfold apply.applierSpec
  iexists ⟨go.GoType.PointerType authApplierV3.ty, #p⟩
  isplitr
  · ipureintro; rfl
  iunfold apply.applierTriples
  isplitr
  · -- Put: the auth applier's
    imodintro
    iintro %r %rq %o %log %F %Pre %Q %Post %info
    imodintro
    iintro %Φ' ⟨Hpre, #HF⟩ HΦ'
    iapply (hPut E c (.ok bi) p r rq o log F Pre Q Post info) $$ [Hpre] HΦ'
    iframe Hpre
    iframe #
  isplitr
  · -- DeleteRange: the auth applier's
    imodintro
    iintro %r %rq %o %log %F %Pre %Q %Post %info
    imodintro
    iintro %Φ' ⟨Hpre, #HF⟩ HΦ'
    iapply (hDel E c (.ok bi) p r rq o log F Pre Q Post info) $$ [Hpre] HΦ'
    iframe Hpre
    iframe #
  isplitr
  · -- Range: the auth applier's
    imodintro
    iintro %r %rq %o %log %info
    imodintro
    iintro %Φ' Hpre HΦ'
    iapply (hRange E c (.ok bi) p r rq o log info) $$ [Hpre] HΦ'
    iframe Hpre
    iframe #
  isplitr
  · -- Txn: the auth applier's
    imodintro
    iintro %r %skip %rq %t %log %F %Pre %Q %Post %info
    imodintro
    iintro %Φ' ⟨Hpre, #HF⟩ HΦ'
    iapply (hTxn E c (.ok bi) p r skip rq t log F Pre Q Post info) $$ [Hpre] HΦ'
    iframe Hpre
    iframe #
  isplitr
  · -- LeaseRevoke: the auth applier's
    imodintro
    iintro %r %rq %id %log %Pre %Q %Post %info
    imodintro
    iintro %Φ' Hpre HΦ'
    iapply (hRev E c (.ok bi) p r rq id log Pre Q Post info) $$ [Hpre] HΦ'
    iframe Hpre
    iframe #
  isplitr
  · -- the methods that leave the log as it is: `UserGet`, `RoleGet` the auth applier's, the
    -- others the inner applier's (promoted)
    imodintro
    iintro %m %r %log %Pre %Q %Post %info %hm
    imodintro
    iintro %Φ' Hpre HΦ'
    simp only [apply.respMethods, List.mem_cons, List.not_mem_nil, _root_.or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    case inr.inr.inr.inr.inr.inr.inr.inr.inl =>
      icases Hpre with ⟨HR, Hm, Hwt, #Hsp⟩
      simp [apply.reqFacts]
      iapply (hUG E c (.ok bi) p r log Pre Q Post info) $$ [HR Hm Hwt]
      · iframe HR Hm Hwt
        iframe #
      inext
      iintro %resp %err ⟨Hpost, #HeI, -⟩
      iapply HΦ'
      iframe Hpost HeI
    case inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inl =>
      icases Hpre with ⟨HR, Hm, Hwt, #Hsp⟩
      simp [apply.reqFacts]
      iapply (hRG E c (.ok bi) p r log Pre Q Post info) $$ [HR Hm Hwt] HΦ'
      iframe HR Hm Hwt
      iframe #
    all_goals
      rw [method_unfold (t := go.GoType.PointerType authApplierV3.ty)]
      wp_call
      wp_auto
      icases Hpre with ⟨HR, Hm, Hwt, #Hsp⟩
      iunfold apply.mPre at Hm
      icases Hm with ⟨Hkv, Hres, Hcs⟩
      ihave ⟨Hi, Hres⟩ := apply.chainRes_auth_out c p (.ok bi) info $$ applierV3 Hres
      iunfold apply.chainResAny at Hres
      icases Hres with ⟨%info', Hres⟩
      iapply HResp $$ %_ %r %log %Pre %Q %Post %info' [] [HR Hkv Hres Hcs Hwt]
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
      iapply apply.chainResAny_auth_in c p (.ok bi) info $$ applierV3 Hi Hres
  isplitr
  · -- `AuthEnable`, `AuthDisable`: the inner applier's (promoted)
    imodintro
    iintro %m %log %Pre %Q %Post %info %hm %hon
    imodintro
    iintro %Φ' Hpre HΦ'
    simp only [apply.resp0Methods, List.mem_cons, List.not_mem_nil, _root_.or_false] at hm
    rcases hm with rfl | rfl
    all_goals
      rw [method_unfold (t := go.GoType.PointerType authApplierV3.ty)]
      wp_call
      wp_auto
      icases Hpre with ⟨Hpre, Hwt, HRW⟩
      iunfold apply.mPre at Hpre
      icases Hpre with ⟨Hkv, Hres, Hcs⟩
      ihave ⟨Hi, Hres⟩ := apply.chainRes_auth_out c p (.ok bi) info $$ applierV3 Hres
      iunfold apply.chainResAny at Hres
      icases Hres with ⟨%info', Hres⟩
      iapply HResp0 $$ %_ %log %Pre %Q %Post %info' [] [] [Hkv Hres Hcs Hwt HRW]
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
      iapply apply.chainResAny_auth_in c p (.ok bi) info $$ applierV3 Hi Hres
  isplitr
  · -- `AuthStatus`: the inner applier's (promoted)
    imodintro
    iintro %log %info
    imodintro
    iintro %Φ' ⟨Hkv, Hres⟩ HΦ'
    rw [method_unfold (t := go.GoType.PointerType authApplierV3.ty) (m := go!"AuthStatus")]
    wp_call
    wp_auto
    ihave ⟨Hi, Hres⟩ := apply.chainRes_auth_out c p (.ok bi) info $$ applierV3 Hres
    iunfold apply.chainResAny at Hres
    icases Hres with ⟨%info', Hres⟩
    iapply HStatus $$ %log %info' [Hkv Hres]
    · iframe
    inext
    iintro %resp %err ⟨Hkv, Hres, #HeI⟩
    iapply HΦ'
    iframe HeI Hkv
    ihave Hres := apply.chainResAny_of _ _ _ $$ Hres
    iapply apply.chainRes_auth_in c p (.ok bi) info $$ applierV3 Hi Hres
  isplitr
  · -- the cluster's methods: the inner applier's (promoted)
    imodintro
    iintro %m %r %v3 %log %Pre %Q %Post %cr %rs %info %hm
    imodintro
    iintro %Φ' Hpre HΦ'
    simp only [apply.clusterMethods, List.mem_cons, List.not_mem_nil, _root_.or_false] at hm
    rcases hm with rfl | rfl | rfl
    all_goals
      rw [method_unfold (t := go.GoType.PointerType authApplierV3.ty)]
      wp_call
      wp_auto
      icases Hpre with ⟨HR, Hm, Hwt, HFS, HRO⟩
      iunfold apply.mPreV at Hm
      icases Hm with ⟨Hkv, Hres, Hcs⟩
      ihave ⟨Hi, Hres⟩ := apply.chainRes_auth_out c p (.ok bi) info $$ applierV3 Hres
      iunfold apply.chainResAny at Hres
      icases Hres with ⟨%info', Hres⟩
      iapply HCluster $$ %_ %r %v3 %log %Pre %Q %Post %cr %rs %info' [] [HR Hkv Hres Hcs Hwt HFS HRO]
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
      ihave Hres := apply.chainResAny_of _ _ _ $$ Hres
      iapply apply.chainRes_auth_in c p (.ok bi) info $$ applierV3 Hi Hres
  · -- `Apply`: the auth applier's
    imodintro
    iintro %r %rq %skip %v3 %af %A %B
    imodintro
    iintro %Φ' Hpre HΦ'
    iapply (hApply E c (.ok bi) p r rq skip v3 af A B) $$ [Hpre] HΦ'
    iframe Hpre
    iframe #

end proof

end EtcdGrove
end Perennial
