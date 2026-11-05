/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.newAuthApplierV3
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.WriteLemmas
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
  intro st base le
  wp_start as -
  iapply wp_fupd
  wp_auto
  irename «$r0» => Hp
  generalize «$r0_ptr» = p at *
  iStructNamed Hp
  ipersist applierV3
  ipersist as'
  ipersist lessor
  imod sync.init_Mutex (apply.authInfoIdle (GF := GF) p) ⊤
      (structFieldRef authApplierV3 go!"mu" p) $$ [mu] [authInfo] with #Hmu
  · iexact mu
  · inext; iunfold apply.authInfoIdle
    first | iexact authInfo | (iExactEq authInfo; rfl)
  imodintro
  iapply HΦ
  iframe applierV3 as' lessor
  isplitr
  · -- (E3k) its structure
    iintro !> %E #Hst #Hle
    iunfold apply.authIs
    iframe applierV3 Hmu
    isplitl
    · iexists st; iframe #
    · iexists le; iframe #
  iintro !> %E %c #Hst #Hle #Hbase
  ihave #Hb := Hbase
  iunfold apply.applierSpec at Hb
  icases Hb with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨#HPut, #HDel, #HRange, #HTxn, #HRev, #HResp, #HResp0, #HStatus, #HCluster,
    #HApply, #HCmp⟩
  ihave #Hauth : apply.authIs E p (.ok bi) $$ []
  · iunfold apply.authIs
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
    iintro %Φ' ⟨Htt, Hpre, #HF⟩ HΦ'
    iapply (hPut E c (.ok bi) p r rq o log F Pre Q Post info) $$ [Hpre Htt] HΦ'
    iframe Hpre Htt
    iframe #
  isplitr
  · -- DeleteRange: the auth applier's
    imodintro
    iintro %r %rq %o %log %F %Pre %Q %Post %info
    imodintro
    iintro %Φ' ⟨Htt, Hpre, #HF⟩ HΦ'
    iapply (hDel E c (.ok bi) p r rq o log F Pre Q Post info) $$ [Hpre Htt] HΦ'
    iframe Hpre Htt
    iframe #
  isplitr
  · -- Range: the auth applier's
    imodintro
    iintro %r %rq %o %log %info
    imodintro
    iintro %Φ' ⟨Htt, Hpre⟩ HΦ'
    iapply (hRange E c (.ok bi) p r rq o log info) $$ [Hpre Htt] HΦ'
    iframe Hpre Htt
    iframe #
  isplitr
  · -- Txn: the auth applier's
    imodintro
    iintro %r %skip %rq %t %log %F %Pre %Q %Post %info
    imodintro
    iintro %Φ' ⟨Htt, Hpre, #HF⟩ HΦ'
    iapply (hTxn E c (.ok bi) p r skip rq t log F Pre Q Post info) $$ [Hpre Htt] HΦ'
    iframe Hpre Htt
    iframe #
  isplitr
  · -- LeaseRevoke: the auth applier's
    imodintro
    iintro %r %rq %id %log %rs %Pre %Q %Post %info
    imodintro
    iintro %Φ' ⟨Htt, Hpre⟩ HΦ'
    iapply (hRev E c (.ok bi) p r rq id log rs Pre Q Post info) $$ [Hpre Htt]
    · iframe Hpre Htt
      iframe #
    inext
    iintro %resp %err ⟨Htt, H1, H2⟩
    iapply HΦ'
    iframe
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
      icases Hpre with ⟨Htt, HR, Hm, #Hsp⟩
      simp [apply.reqFacts]
      iapply (hUG E c (.ok bi) p r log Pre Q Post info) $$ [HR Hm Htt]
      · iframe HR Hm Htt
        iframe #
      inext
      iintro %resp %err ⟨Htt, Hpost, #HeI, -⟩
      iapply HΦ'
      iframe Htt
      iframe Hpost HeI
    case inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inl =>
      icases Hpre with ⟨Htt, HR, Hm, #Hsp⟩
      simp [apply.reqFacts]
      iapply (hRG E c (.ok bi) p r log Pre Q Post info) $$ [HR Hm Htt] HΦ'
      iframe HR Hm Htt
      iframe #
    all_goals
      rw [method_unfold (t := go.GoType.PointerType authApplierV3.ty)]
      wp_call
      wp_auto
      icases Hpre with ⟨Htt, HR, Hm, #Hsp⟩
      icases apply.mPreW_split_chain _ _ _ _ _ _ _ _ $$ Hm with ⟨Hkv, Hres⟩
      ihave ⟨Hi, Hres⟩ := apply.chainRes_auth_out c p (.ok bi) info $$ applierV3 Hres
      iunfold apply.chainResAny at Hres
      icases Hres with ⟨%info', Hres⟩
      iapply HResp $$ %_ %r %log %Pre %Q %Post %info' [] [Htt HR Hkv Hres]
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
      icases Hpre with ⟨Htt, Hpre, HRW⟩
      icases apply.mPreW_split_chain _ _ _ _ _ _ _ _ $$ Hpre with ⟨Hkv, Hres⟩
      ihave ⟨Hi, Hres⟩ := apply.chainRes_auth_out c p (.ok bi) info $$ applierV3 Hres
      iunfold apply.chainResAny at Hres
      icases Hres with ⟨%info', Hres⟩
      iapply HResp0 $$ %_ %log %Pre %Q %Post %info' [] [] [Htt Hkv Hres HRW]
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
      iapply apply.chainResAny_auth_in c p (.ok bi) info $$ applierV3 Hi Hres
  isplitr
  · -- `AuthStatus`: the inner applier's (promoted)
    imodintro
    iintro %log %info
    imodintro
    iintro %Φ' ⟨Htt, Hkv, Hres⟩ HΦ'
    rw [method_unfold (t := go.GoType.PointerType authApplierV3.ty) (m := go!"AuthStatus")]
    wp_call
    wp_auto
    ihave ⟨Hi, Hres⟩ := apply.chainRes_auth_out c p (.ok bi) info $$ applierV3 Hres
    iunfold apply.chainResAny at Hres
    icases Hres with ⟨%info', Hres⟩
    iapply HStatus $$ %log %info' [Htt Hkv Hres]
    · iframe
    inext
    iintro %resp %err ⟨Htt, Hkv, Hres, #HeI⟩
    iapply HΦ'
    iframe Htt HeI Hkv
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
      icases Hpre with ⟨HR, Hm, HFS, HRO⟩
      icases apply.mPreV_split_chain _ _ _ _ _ _ _ _ _ $$ Hm with ⟨Hkv, Hres⟩
      ihave ⟨Hi, Hres⟩ := apply.chainRes_auth_out c p (.ok bi) info $$ applierV3 Hres
      iunfold apply.chainResAny at Hres
      icases Hres with ⟨%info', Hres⟩
      iapply HCluster $$ %_ %r %v3 %log %Pre %Q %Post %cr %rs %info' [] [HR Hkv Hres HFS HRO]
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
      ihave Hres := apply.chainResAny_of _ _ _ $$ Hres
      iapply apply.chainRes_auth_in c p (.ok bi) info $$ applierV3 Hi Hres
  isplitr
  · -- `Apply`: the auth applier's
    imodintro
    iintro %r %rq %skip %v3 %af %A %B
    imodintro
    iintro %Φ' Hpre HΦ'
    iapply (hApply E c (.ok bi) p r rq skip v3 af A B) $$ [Hpre] HΦ'
    iframe Hpre
    iframe #
  · -- `Compaction`: the inner applier's (promoted; the auth layer checks nothing)
    iunfold apply.cmpTriple
    iunfold apply.cmpTriple at HCmp
    imodintro
    iintro %cr %rev %log %crev %Pre %Q %Post %info
    imodintro
    iintro %Φ' ⟨#Hcr, %Hadm, HCp, Htt, Hm, Hc⟩ HΦ'
    rw [method_unfold (t := go.GoType.PointerType authApplierV3.ty) (m := go!"Compaction")]
    wp_call
    wp_auto
    icases apply.mPre_split_chain _ _ _ _ _ _ _ _ $$ Hm with ⟨Hkv, Hres⟩
    ihave ⟨Hi, Hres⟩ := apply.chainRes_auth_out c p (.ok bi) info $$ applierV3 Hres
    iunfold apply.chainResAny at Hres
    icases Hres with ⟨%info', Hres⟩
    iapply HCmp $$ %cr %rev %log %crev %Pre %Q %Post %info' [HCp Htt Hkv Hres Hc]
    · iframe HCp Htt Hc; iframe #; isplitr; · ipureintro; exact Hadm
      iapply apply.mPre_of_rest; iframe
    inext
    iintro %resp %ch %trace %err ⟨Htt, Hkv, Hres, HPP, Hc, Hans⟩
    iapply HΦ'
    iframe Htt
    rw [apply.chainCompacts_auth E.authOn c, apply.cmpAnswerIs_congr (.auth E.authOn c) c (apply.chainCompacts_auth E.authOn c)]
    iframe Hkv HPP
    isplitr [Hc Hans]
    rotate_left
    · isplitl [Hc]
      · iexact Hc
      · iexact Hans
    ihave Hres := apply.chainResAny_of _ _ _ $$ Hres
    iapply apply.chainRes_auth_in c p (.ok bi) info $$ applierV3 Hi Hres

end proof

end EtcdGrove
end Perennial
