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
  intro E c st base le
  wp_start as ⟨#Hst, #Hle, #Hbase⟩
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
  ipersist as'
  ipersist lessor
  imod sync.init_Mutex (apply.authInfoOwn (GF := GF) p) ⊤ (structFieldRef authApplierV3 go!"mu" p)
    $$ [mu] [authInfo] with #Hmu
  · iexact mu
  · inext; iunfold apply.authInfoOwn; iexists _; iexact authInfo
  ihave #Hauth : apply.authIs E p (.ok bi) $$ []
  · iunfold apply.authIs
    iframe applierV3 Hmu
    isplitl
    · iexists st; iframe #
    · iexists le; iframe #
  wp_auto
  iapply HΦ
  iunfold apply.applierSpec
  iexists ⟨go.GoType.PointerType authApplierV3.ty, #p⟩
  isplitr
  · ipureintro; rfl
  iunfold apply.applierTriples
  isplitr
  · -- Put: the auth applier's
    imodintro
    iintro %r %rq %o %log %Pre %Q %Post
    imodintro
    iintro %Φ' Hpre HΦ'
    iapply (hPut E c (.ok bi) p r rq o log Pre Q Post) $$ [Hpre] HΦ'
    iframe Hpre
    iframe #
  isplitr
  · -- DeleteRange: the auth applier's
    imodintro
    iintro %r %rq %o %log %Pre %Q %Post
    imodintro
    iintro %Φ' Hpre HΦ'
    iapply (hDel E c (.ok bi) p r rq o log Pre Q Post) $$ [Hpre] HΦ'
    iframe Hpre
    iframe #
  isplitr
  · -- Range: the auth applier's
    imodintro
    iintro %r %rq %o %log
    imodintro
    iintro %Φ' Hpre HΦ'
    iapply (hRange E c (.ok bi) p r rq o log) $$ [Hpre] HΦ'
    iframe Hpre
    iframe #
  isplitr
  · -- Txn: the auth applier's
    imodintro
    iintro %r %skip %rq %t %log %Pre %Q %Post
    imodintro
    iintro %Φ' Hpre HΦ'
    iapply (hTxn E c (.ok bi) p r skip rq t log Pre Q Post) $$ [Hpre] HΦ'
    iframe Hpre
    iframe #
  isplitr
  · -- LeaseRevoke: the auth applier's
    imodintro
    iintro %r %rq %id %log %Pre %Q %Post
    imodintro
    iintro %Φ' Hpre HΦ'
    iapply (hRev E c (.ok bi) p r rq id log Pre Q Post) $$ [Hpre] HΦ'
    iframe Hpre
    iframe #
  isplitr
  · -- the methods that leave the log as it is: `UserGet`, `RoleGet` the auth applier's, the
    -- others the inner applier's (promoted)
    imodintro
    iintro %m %r %log %Pre %Q %Post %hm
    imodintro
    iintro %Φ' Hpre HΦ'
    simp only [apply.respMethods, List.mem_cons, List.not_mem_nil, _root_.or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    case inr.inr.inr.inr.inr.inr.inr.inr.inl =>
      icases Hpre with ⟨HR, Hm⟩
      simp [apply.reqFacts]
      iapply (hUG E c (.ok bi) p r log Pre Q Post) $$ [HR Hm] HΦ'
      iframe HR Hm
      iframe #
    case inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inr.inl =>
      icases Hpre with ⟨HR, Hm⟩
      simp [apply.reqFacts]
      iapply (hRG E c (.ok bi) p r log Pre Q Post) $$ [HR Hm] HΦ'
      iframe HR Hm
      iframe #
    all_goals
      rw [method_unfold (t := go.GoType.PointerType authApplierV3.ty)]
      wp_call
      wp_auto
      icases Hpre with ⟨HR, Hm⟩
      iunfold apply.mPre at Hm
      icases Hm with ⟨Hkv, Hres, Hcs⟩
      ihave ⟨Hi, Hres⟩ := apply.chainRes_auth_out c p (.ok bi) $$ applierV3 Hres
      iapply HResp $$ %_ %r %log %Pre %Q %Post [] [HR Hkv Hres Hcs]
      · ipureintro; simp [apply.respMethods]
      · iframe HR
        iunfold apply.mPre
        iframe
      inext
      iintro %resp %err Hpost
      iapply HΦ'
      iunfold apply.mPost at Hpost
      iunfold apply.mPost
      icases Hpost with ⟨Hkv, Hres, HPP⟩
      iframe Hkv HPP
      iapply apply.chainRes_auth_in c p (.ok bi) $$ applierV3 Hi Hres
  isplitr
  · -- `AuthEnable`, `AuthDisable`: the inner applier's (promoted)
    imodintro
    iintro %m %log %Pre %Q %Post %hm
    imodintro
    iintro %Φ' Hpre HΦ'
    simp only [apply.resp0Methods, List.mem_cons, List.not_mem_nil, _root_.or_false] at hm
    rcases hm with rfl | rfl
    all_goals
      rw [method_unfold (t := go.GoType.PointerType authApplierV3.ty)]
      wp_call
      wp_auto
      iunfold apply.mPre at Hpre
      icases Hpre with ⟨Hkv, Hres, Hcs⟩
      ihave ⟨Hi, Hres⟩ := apply.chainRes_auth_out c p (.ok bi) $$ applierV3 Hres
      iapply HResp0 $$ %_ %log %Pre %Q %Post [] [Hkv Hres Hcs]
      · ipureintro; simp [apply.resp0Methods]
      · iunfold apply.mPre
        iframe
      inext
      iintro %resp %err Hpost
      iapply HΦ'
      iunfold apply.mPost at Hpost
      iunfold apply.mPost
      icases Hpost with ⟨Hkv, Hres, HPP⟩
      iframe Hkv HPP
      iapply apply.chainRes_auth_in c p (.ok bi) $$ applierV3 Hi Hres
  isplitr
  · -- `AuthStatus`: the inner applier's (promoted)
    imodintro
    iintro %log
    imodintro
    iintro %Φ' ⟨Hkv, Hres⟩ HΦ'
    rw [method_unfold (t := go.GoType.PointerType authApplierV3.ty) (m := go!"AuthStatus")]
    wp_call
    wp_auto
    ihave ⟨Hi, Hres⟩ := apply.chainRes_auth_out c p (.ok bi) $$ applierV3 Hres
    iapply HStatus $$ %log [Hkv Hres]
    · iframe
    inext
    iintro %resp %err ⟨Hkv, Hres⟩
    iapply HΦ'
    iframe Hkv
    iapply apply.chainRes_auth_in c p (.ok bi) $$ applierV3 Hi Hres
  isplitr
  · -- the cluster's methods: the inner applier's (promoted)
    imodintro
    iintro %m %r %v3 %log %Pre %Q %Post %hm
    imodintro
    iintro %Φ' Hpre HΦ'
    simp only [apply.clusterMethods, List.mem_cons, List.not_mem_nil, _root_.or_false] at hm
    rcases hm with rfl | rfl | rfl
    all_goals
      rw [method_unfold (t := go.GoType.PointerType authApplierV3.ty)]
      wp_call
      wp_auto
      icases Hpre with ⟨HR, Hm⟩
      iunfold apply.mPre at Hm
      icases Hm with ⟨Hkv, Hres, Hcs⟩
      ihave ⟨Hi, Hres⟩ := apply.chainRes_auth_out c p (.ok bi) $$ applierV3 Hres
      iapply HCluster $$ %_ %r %v3 %log %Pre %Q %Post [] [HR Hkv Hres Hcs]
      · ipureintro; simp [apply.clusterMethods]
      · iframe HR
        iunfold apply.mPre
        iframe
      inext
      iintro Hpost
      iapply HΦ'
      iunfold apply.mPost at Hpost
      iunfold apply.mPost
      icases Hpost with ⟨Hkv, Hres, HPP⟩
      iframe Hkv HPP
      iapply apply.chainRes_auth_in c p (.ok bi) $$ applierV3 Hi Hres
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
