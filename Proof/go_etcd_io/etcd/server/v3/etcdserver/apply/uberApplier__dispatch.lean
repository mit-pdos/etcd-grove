/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier__dispatch
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier__Alarm
public import Spec.errors.Is
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.ApplySecObserve
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.WarnOfExpensiveRequest
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.WarnOfFailedRequest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.DispatchLemmas

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

set_option hygiene false in
/-- Persist the result struct `ar` (all stores done) and split it into its fields (read-only
from now on: the deferred metrics read `Resp` and `Err`). -/
local macro "persist_ar" : tactic => `(tactic| (
  ihave ⟨H0, %hn⟩ := typedPointsto_not_null_dup _ _ _ $$ «$r0»
  ipersist H0
  ihave #H0' := H0
  iStructNamed H0'))

set_option hygiene false in
/-- The deferred metrics with `success` (`ar.Err == nil`). -/
local macro "ok_path" : tactic => `(tactic| (
  wp_apply time.wp_Since as %d -
  wp_apply hASO
  wp_alloc s1 as Hs1
  wp_auto
  wp_apply hWER))

set_option hygiene false in
/-- The deferred metrics with `ar.Err` not nil: `errors.Is(ar.Err, ErrCompacted)`, then the
warnings (the failure's if not `success`). -/
local macro "err_path" : tactic => `(tactic| (
  ihave #HeIu := applyErrIs_tree _ $$ HeI
  ihave ⟨%S, %M, #Htree, %HS⟩ := HeIu $$ %(GoInterface.ok ec)
  wp_apply (hIs S M _ (GoInterface.ok ec) (fun tii h => by cases h; exact Hecl.1)
    (HS.2 (fun tii h => by cases h; exact Hecl.1)))
    $$ [] as %b -
  · iframe Htree; ipureintro; exact HS.1
  wp_apply time.wp_Since as %d -
  wp_apply hASO
  wp_alloc s1 as Hs1
  wp_auto
  wp_apply hWER
  cases b <;> (try wp_auto) <;> (try (wp_alloc s2 as Hs2; wp_auto; wp_apply hWFR))))

set_option hygiene false in
/-- The deferred metrics, whatever `ar.Err`. -/
local macro "dtail" : tactic => `(tactic| (
  cases err <;> (try wp_auto) <;> first | ok_path | err_path))

set_option hygiene false in
/-- The postcondition for a request that leaves the KV and the chain as they are. -/
local macro "fin_same" : tactic => `(tactic| (
  iframe Hres
  iexists (GoInterface.ok ai), c, (Outcome.applied log false)
  simp only [apply.Outcome.logAfter]
  iframe Ha Hs Hkv
  isplitl [HPP]
  · simp only [apply.cPost, ↓reduceIte]; iexact HPP
  isplitr
  · ipureintro; simp [apply.dispatchStep, apply.chainAfter, hk, apply.preV3Kind, apply.storeKind, apply.Outcome.logAfter]
  simp only [apply.dispatchResult, hk, apply.preV3Kind, _root_.true_or, _root_.or_true, ↓reduceIte]
  iframe %hn
  iexists _
  iframe H0
  isplitl; rotate_left
  · first | iexact HeI | iapply applyErrIs_nil
  simp only [apply.dispatchAnswer, hk]))

set_option hygiene false in
/-- The postcondition for a request whose outcome `oc` is the chain's (`Hst`). -/
local macro "fin_kv" : tactic => `(tactic| (
  iframe Hres
  iexists (GoInterface.ok ai), c, oc
  iframe Ha Hs Hkv
  isplitl [HPP]
  · simp only [apply.cPost, ↓reduceIte]; iexact HPP
  isplitr
  · ipureintro
    refine ⟨?_, Or.inl rfl⟩
    simp only [apply.dispatchStep, hk, apply.preV3Kind, apply.storeKind,
      Bool.false_eq_true, _root_.or_self, ↓reduceIte]
    exact Hst
  simp only [apply.dispatchResult, hk, apply.preV3Kind, _root_.or_true, ↓reduceIte]
  iframe %hn
  iexists _
  iframe H0
  isplitl; rotate_left
  · first | iexact HeI | iapply applyErrIs_nil
  simp only [apply.dispatchAnswer, hk]))

set_option hygiene false in
/-- A case of the second `switch` at the join point (`R` of the `wp_join` below): `ar` (made
read-only) and `op` as computed, then the postcondition of `dispatch` at `ar`. -/
local macro "join_ar" : tactic => `(tactic| (
  wp_join_done
  persist_ar
  imodintro
  iexists _, _, _, _, _
  iframe a r ar op H0 HeI))

-- (the unused-variables linter walks the whole info tree of this long proof: 10-15s of
-- the build of this module, which is on the build's critical path)
set_option linter.unusedVariables false in
set_option maxHeartbeats 10000000 in
theorem apply.uberApplier.dispatch.wp_proof
    (hIs : errors.Is.spec (GF := GF) (hG := hG))
    (hASO : txn.ApplySecObserve.spec (GF := GF) (hG := hG))
    (hWER : txn.WarnOfExpensiveRequest.spec (GF := GF) (hG := hG))
    (hWFR : txn.WarnOfFailedRequest.spec (GF := GF) (hG := hG))
    (hAlarm : apply.uberApplier.Alarm.spec (GF := GF) (hG := hG)) :
    apply.uberApplier.dispatch.spec (GF := GF) (hG := hG) := by
  intro E p opts c a r rq skip v3 log Pre Q Post
  wp_start as ⟨#Hu, #Hw, Hres, Ha, #Hs, Hkv, Hwt, Hc, %Hok⟩
  ihave #Hu' := Hu
  iunfold apply.uberIs at Hu'
  icases Hu' with ⟨%Hpn, #Hopts, #Hlg, #Has, #Hwad, %base, #Hbase, #Hbs⟩
  ihave #Hw' := Hw
  iunfold apply.irrWrapperIs at Hw'
  icases Hw' with ⟨%Hrn, %ip, #Hip, #Hirr, #Hskip⟩
  ihave #Hirr' := Hirr
  iunfold apply.internalRaftRequestIs at Hirr'
  icases Hirr' with ⟨%Hipn, #FID, ⟨%lHd, #FHd, #HHd⟩, ⟨%lRa, #FRa, #HRa⟩, ⟨%lPu, #FPu, #HPu⟩,
    ⟨%lDe, #FDe, #HDe⟩, ⟨%lTx, #FTx, #HTx⟩, ⟨%lCo, #FCo, #HCo⟩, ⟨%lLG, #FLG, #HLG⟩,
    ⟨%lLR, #FLR, #HLR⟩, ⟨%lAl, #FAl, #HAl⟩, ⟨%lLC, #FLC, #HLC⟩, ⟨%lAE, #FAE, #HAE⟩,
    ⟨%lAD, #FAD, #HAD⟩, ⟨%lAS, #FAS, #HAS⟩, ⟨%lAu, #FAu, #HAu⟩, ⟨%lUA, #FUA, #HUA⟩,
    ⟨%lUD, #FUD, #HUD⟩, ⟨%lUG, #FUG, #HUG⟩, ⟨%lUC, #FUC, #HUC⟩, ⟨%lUGR, #FUGR, #HUGR⟩,
    ⟨%lURR, #FURR, #HURR⟩, ⟨%lUL, #FUL, #HUL⟩, ⟨%lRL, #FRL, #HRL⟩, ⟨%lRA, #FRA, #HRA⟩,
    ⟨%lRD, #FRD, #HRD⟩, ⟨%lRG, #FRG, #HRG⟩, ⟨%lRGP, #FRGP, #HRGP⟩, ⟨%lRRP, #FRRP, #HRRP⟩,
    ⟨%lCV, #FCV, #HCV⟩, ⟨%lCM, #FCM, #HCM⟩, ⟨%lDI, #FDI, #HDI⟩, ⟨%lDT, #FDT, #HDT⟩⟩
  ihave %nRa := apply.optReqIs_null _ _ _ (apply.rangeIs_nn lRa) $$ HRa
  ihave %nPu := apply.optReqIs_null _ _ _ (apply.putIs_nn lPu) $$ HPu
  ihave %nDe := apply.optReqIs_null _ _ _ (apply.deleteIs_nn lDe) $$ HDe
  ihave %nTx := apply.optReqIs_null _ _ _ (apply.txnIs_nn lTx) $$ HTx
  ihave %nCo := apply.optReqIs_null _ _ _ (apply.compactionIs_nn lCo) $$ HCo
  ihave %nLG := apply.optReqIs_null _ _ _ (apply.leaseGrantIs_nn lLG) $$ HLG
  ihave %nLR := apply.optReqIs_null _ _ _ (apply.leaseRevokeIs_nn lLR) $$ HLR
  ihave %nAl := apply.optReqIs_null _ _ _ (apply.alarmRequestIs_nn lAl) $$ HAl
  ihave %nLC := apply.optReqIs_null _ _ _ (apply.leaseCheckpointIs_nn lLC) $$ HLC
  ihave %nAu := apply.optReqIs_null _ _ _ (apply.authenticateIs_nn lAu) $$ HAu
  ihave %nUG := apply.optReqIs_null _ _ _ (apply.authUserGetIs_nn lUG) $$ HUG
  ihave %nRG := apply.optReqIs_null _ _ _ (apply.authRoleGetIs_nn lRG) $$ HRG
  ihave %nCV := apply.optReqIs_null _ _ _ (apply.clusterVersionSetIs_nn lCV) $$ HCV
  ihave %nCM := apply.optReqIs_null _ _ _ (apply.memberAttrSetIs_nn lCM) $$ HCM
  ihave %nDI := apply.optReqIs_null _ _ _ (apply.downgradeInfoSetIs_nn lDI) $$ HDI
  ihave %nAE := apply.presentIs_null _ _ $$ HAE
  ihave %nAD := apply.presentIs_null _ _ $$ HAD
  ihave %nAS := apply.presentIs_null _ _ $$ HAS
  ihave %nUA := apply.presentIs_null _ _ $$ HUA
  ihave %nUD := apply.presentIs_null _ _ $$ HUD
  ihave %nUC := apply.presentIs_null _ _ $$ HUC
  ihave %nUGR := apply.presentIs_null _ _ $$ HUGR
  ihave %nURR := apply.presentIs_null _ _ $$ HURR
  ihave %nUL := apply.presentIs_null _ _ $$ HUL
  ihave %nRL := apply.presentIs_null _ _ $$ HRL
  ihave %nRA := apply.presentIs_null _ _ $$ HRA
  ihave %nRD := apply.presentIs_null _ _ $$ HRD
  ihave %nRGP := apply.presentIs_null _ _ $$ HRGP
  ihave %nRRP := apply.presentIs_null _ _ $$ HRRP
  ihave %nDT := apply.presentIs_null _ _ $$ HDT
  ihave #Hsp := Hs
  iunfold apply.applierSpec at Hsp
  icases Hsp with ⟨%ai, %Hai, #Ht⟩
  subst Hai
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨#HPut, #HDel, #HRange, #HTxn, #HRev, #HResp, #HResp0, #HStatus, #HCluster, -⟩
  ihave #Hmp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  ihave Hinit : (go_etcd_io.etcd.server.v3.storage.mvcc.mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hmp
  iclear Hinit
  ihave Hai : (go_etcd_io.etcd.server.v3.etcdserver.apply.applyInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨-, -, #Hev⟩
  ihave #Hev' := Hev
  icases Hev' with ⟨-, -, -, -, -, #HCpl⟩
  iunfold errVarLeaf at HCpl
  icases HCpl with ⟨%ec, #Hcomp, %Hecl, -⟩
  ihave #Perr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Ptxn : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  wp_apply time.wp_Now as %start -
  wp_if_destruct
  · -- ClusterVersionSet
    have hl : lCV ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nCV.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HCV
    have hk : dispatchKind rq = .clusterVersionSet := by simp [dispatchKind, hs]
    have hsv : semverValid x := by
      have := Hok.1; simp only [rqOk, hk] at this; exact this x hs
    wp_apply HCluster $$ %go!"ClusterVersionSet" %lCV %v3 %log %Pre %Q %Post [] [Hkv Hres Hc] as Hpost
    · ipureintro; simp [apply.clusterMethods]
    · simp (config := {decide := true}) only [apply.reqFacts, ↓reduceIte]
      iunfold apply.mPreV
      iframe
      iexists x; iframe HR; ipureintro; exact hsv
    persist_ar
    ok_path
    iapply HΦ
    iunfold apply.mPostV at Hpost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    fin_same
    ipureintro; exact ⟨rfl, rfl⟩
  have zClusterVersionSet : rq.clusterVersionSet = none := nCV.1 (by simpa using Hif)
  wp_if_destruct
  · -- ClusterMemberAttrSet
    have hl : lCM ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nCM.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HCM
    have hk : dispatchKind rq = .clusterMemberAttrSet := by simp [dispatchKind, zClusterVersionSet, hs]
    wp_apply HCluster $$ %go!"ClusterMemberAttrSet" %lCM %v3 %log %Pre %Q %Post [] [Hkv Hres Hc] as Hpost
    · ipureintro; simp [apply.clusterMethods]
    · simp (config := {decide := true}) only [apply.reqFacts, ↓reduceIte]
      iunfold apply.mPreV
      iframe
      iexists x; iframe HR
    persist_ar
    ok_path
    iapply HΦ
    iunfold apply.mPostV at Hpost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    fin_same
    ipureintro; exact ⟨rfl, rfl⟩
  have zClusterMemberAttrSet : rq.clusterMemberAttrSet = none := nCM.1 (by simpa using Hif)
  wp_if_destruct
  · -- DowngradeInfoSet
    have hl : lDI ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nDI.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HDI
    have hk : dispatchKind rq = .downgradeInfoSet := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, hs]
    wp_apply HCluster $$ %go!"DowngradeInfoSet" %lDI %v3 %log %Pre %Q %Post [] [Hkv Hres Hc] as Hpost
    · ipureintro; simp [apply.clusterMethods]
    · simp (config := {decide := true}) only [apply.reqFacts, ↓reduceIte]
      iunfold apply.mPreV
      iframe
      iexists x; iframe HR
    persist_ar
    ok_path
    iapply HΦ
    iunfold apply.mPostV at Hpost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    fin_same
    ipureintro; exact ⟨rfl, rfl⟩
  have zDowngradeInfoSet : rq.downgradeInfoSet = none := nDI.1 (by simpa using Hif)
  wp_if_destruct
  · -- DowngradeVersionTest: nothing
    have hl : lDT ≠ null := by simpa using Hif
    have hs : rq.downgradeVersionTest = true := by
      cases h : rq.downgradeVersionTest
      · exact absurd (nDT.2 h) hl
      · rfl
    have hk : dispatchKind rq = .downgradeVersionTest := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, hs]
    persist_ar
    ok_path
    iapply HΦ
    ihave HPP : iprop(cPost v3 Pre Post) $$ [Hc]
    · iapply apply.cPost_of_pre; iapply apply.cPre_pre; iexact Hc
    fin_same
    ipureintro; exact ⟨rfl, rfl⟩
  have zDowngradeVersionTest : rq.downgradeVersionTest = false := nDT.1 (by simpa using Hif)
  have hpre : apply.preV3Kind (dispatchKind rq) = false :=
    apply.preV3Kind_dispatchKind rq zClusterVersionSet zClusterMemberAttrSet zDowngradeInfoSet zDowngradeVersionTest
  cases v3
  · -- not `shouldApplyV3`: nil
    (try wp_auto)
    ok_path
    iapply HΦ
    iframe Hres
    iexists (GoInterface.ok ai), c, (Outcome.applied log false)
    simp only [apply.Outcome.logAfter]
    iframe Ha Hs Hkv
    isplitl [Hc]
    · simp only [apply.cPost, apply.cPre, Bool.false_eq_true, ↓reduceIte]; iexact Hc
    isplitr
    · ipureintro; simp [apply.dispatchStep, apply.chainAfter, hpre]
    simp only [apply.dispatchResult, hpre, Bool.false_eq_true, or_self, ↓reduceIte]
    ipureintro; trivial
  (try wp_auto)
  ihave Hc : iprop(mvcc.csContract E.P E.f Pre Q Post) $$ [Hc]
  · simp only [apply.cPre, ↓reduceIte]; iexact Hc
  -- the second `switch`: each case computes `ar` and `op` and establishes the postcondition
  -- at `ar`; the `return` and the deferred metrics, after the join, are verified once (not
  -- once per request kind)
  wp_join iprop(|==> ∃ (resp : google_golang_org.protobuf.reflect.protoreflect.ProtoMessage)
      (err : GoError) (physc : GoChan) (trace : Loc) (opS : GoString),
      a_ptr ↦ p ∗ r_ptr ↦ r ∗ ar_ptr ↦ «$r0_ptr» ∗ op_ptr ↦ opS ∗
      «$r0_ptr» ↦□ Result.mk resp err physc trace ∗ applyErrIs err ∗
      (apply.chainRes c (GoInterface.ok ai) ∗
        ∃ (a' : GoInterface) (c' : apply.Chain) (o : apply.Outcome),
          structFieldRef uberApplier go!"applyV3" p ↦ a' ∗ apply.applierSpec E c' a' ∗
          apply.kvOwn E (o.logAfter log) ∗ apply.cPost true Pre Post ∗
          ⌜apply.dispatchStep c rq true log o ∧ apply.chainAfter rq true c c'⌝ ∗
          apply.dispatchResult rq true log skip «$r0_ptr» o))
    with [a r ar op «$r0» Hc Hres Ha Hkv Hwt]
  · -- Range
    have hl : lRa ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nRa.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HRa
    have hk : dispatchKind rq = .range := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, hs]
    have hok := Hok.1
    simp only [rqOk, hk] at hok
    wp_apply HRange $$ %lRa %rq %x %log [Hkv Hres] as %resp %trace %err Hpost
    · iunfold apply.rangePre
      isplitr
      · ipureintro; exact ⟨hs, hk, hok x hs⟩
      iframe HR
      iframe
    iunfold apply.rangePost at Hpost
    icases Hpost with ⟨%oc, %Hst, Hans, Hkv, Hres⟩
    ihave ⟨Hans, #HeI⟩ := apply.keep_errIs (apply.rangeOutcomeIs_errIs _ _ _ _ _) $$ [$Hev $Hans]
    join_ar
    ihave HPP : iprop(Post ∨ Pre) $$ [Hc]
    · iright; iapply apply.csContract_pre; iexact Hc
    fin_kv
    iexists x, resp; iframe Hans; ipureintro; exact ⟨hs, rfl⟩
  have zRange : rq.range = none := nRa.1 (by simpa using Hif)
  wp_if_destruct
  · -- Put
    have hl : lPu ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nPu.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HPu
    have hk : dispatchKind rq = .put := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, hs]
    have hok := Hok.1
    simp only [rqOk, hk] at hok
    wp_apply HPut $$ %lPu %rq %x %log %Pre %Q %Post [Hkv Hwt Hres Hc] as %resp %trace %err Hpost
    · iunfold apply.putPre
      isplitr
      · ipureintro; exact ⟨hs, hk, hok⟩
      iframe HR
      iunfold apply.mPre
      iframe
    iunfold apply.kvPost at Hpost
    icases Hpost with ⟨%oc, %Hst, Hans, Hkv, Hres, HPP⟩
    ihave ⟨Hans, #HeI⟩ := apply.keep_errIs (apply.putAnswerIs_errIs _ _ _ _ _) $$ [$Hev $Hans]
    join_ar
    fin_kv
    iexists x, resp; iframe Hans; ipureintro; exact ⟨hs, rfl⟩
  have zPut : rq.put = none := nPu.1 (by simpa using Hif)
  wp_if_destruct
  · -- DeleteRange
    have hl : lDe ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nDe.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HDe
    have hk : dispatchKind rq = .deleteRange := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, hs]
    have hok := Hok.1
    simp only [rqOk, hk] at hok
    wp_apply HDel $$ %lDe %rq %x %log %Pre %Q %Post [Hkv Hwt Hres Hc] as %resp %trace %err Hpost
    · iunfold apply.deletePre
      isplitr
      · ipureintro; exact ⟨hs, hk, hok x hs⟩
      iframe HR
      iunfold apply.mPre
      iframe
    iunfold apply.kvPost at Hpost
    icases Hpost with ⟨%oc, %Hst, Hans, Hkv, Hres, HPP⟩
    ihave ⟨Hans, #HeI⟩ := apply.keep_errIs (apply.deleteAnswerIs_errIs _ _ _ _ _) $$ [$Hev $Hans]
    join_ar
    fin_kv
    iexists x, resp; iframe Hans; ipureintro; exact ⟨hs, rfl⟩
  have zDeleteRange : rq.deleteRange = none := nDe.1 (by simpa using Hif)
  wp_if_destruct
  · -- Txn
    have hl : lTx ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nTx.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HTx
    have hk : dispatchKind rq = .txn := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, hs]
    have hok := Hok.1
    simp only [rqOk, hk] at hok
    wp_apply HTxn $$ %lTx %skip %rq %x %log %Pre %Q %Post [Hkv Hwt Hres Hc] as %resp %trace %err Hpost
    · iunfold apply.txnPre
      isplitr
      · ipureintro; exact ⟨hs, hk, hok x hs⟩
      iframe HR
      iunfold apply.mPre
      iframe
    iunfold apply.kvPost at Hpost
    icases Hpost with ⟨%oc, %Hst, Hans, Hkv, Hres, HPP⟩
    ihave ⟨Hans, #HeI⟩ := apply.keep_errIs (apply.txnAnswerIs_errIs _ _ _ _ _ _) $$ [$Hev $Hans]
    join_ar
    fin_kv
    iexists x, resp; iframe Hans; ipureintro; exact ⟨hs, rfl⟩
  have zTxn : rq.txn = none := nTx.1 (by simpa using Hif)
  wp_if_destruct
  · -- Compaction: out of the model (the premise `dispatchOk`)
    have hl : lCo ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nCo.2 h))
    have hk : dispatchKind rq = .compaction := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, hs]
    exact absurd hk Hok.2.1
  have zCompaction : rq.compaction = none := nCo.1 (by simpa using Hif)
  wp_if_destruct
  · -- LeaseGrant
    have hl : lLG ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nLG.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HLG
    have hk : dispatchKind rq = .leaseGrant := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, hs]
    have hok := Hok.1
    simp only [rqOk, hk] at hok
    wp_apply HResp $$ %go!"LeaseGrant" %lLG %log %Pre %Q %Post [] [Hkv Hres Hc] as %resp %err ⟨Hpost, #HeI⟩
    · ipureintro; simp [apply.respMethods]
    · simp (config := {decide := true}) only [apply.reqFacts, ↓reduceIte]
      iunfold apply.mPre
      iframe; iexists x; iframe HR
    iunfold apply.mPost at Hpost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    join_ar
    fin_same
    itrivial
  have zLeaseGrant : rq.leaseGrant = none := nLG.1 (by simpa using Hif)
  wp_if_destruct
  · -- LeaseRevoke
    have hl : lLR ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nLR.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HLR
    have hk : dispatchKind rq = .leaseRevoke := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, hs]
    have hok := Hok.1
    simp only [rqOk, hk] at hok
    wp_apply HRev $$ %lLR %rq %x %log %Pre %Q %Post [Hkv Hwt Hres Hc] as %resp %err Hpost
    · iunfold apply.revokePre
      isplitr
      · ipureintro; exact ⟨hs, hk⟩
      iframe HR
      iunfold apply.mPre
      iframe
    iunfold apply.kvPost at Hpost
    icases Hpost with ⟨%oc, %Hst, Hans, Hkv, Hres, HPP⟩
    ihave ⟨Hans, #HeI⟩ := apply.keep_errIs (apply.revokeOutcomeIs_errIs _ _ _) $$ [$Hev $Hans]
    join_ar
    fin_kv
    iexists resp; iframe Hans; ipureintro; rfl
  have zLeaseRevoke : rq.leaseRevoke = none := nLR.1 (by simpa using Hif)
  wp_if_destruct
  · -- LeaseCheckpoint
    have hl : lLC ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nLC.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HLC
    have hk : dispatchKind rq = .leaseCheckpoint := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, hs]
    have hok := Hok.1
    simp only [rqOk, hk] at hok
    wp_apply HResp $$ %go!"LeaseCheckpoint" %lLC %log %Pre %Q %Post [] [Hkv Hres Hc] as %resp %err ⟨Hpost, #HeI⟩
    · ipureintro; simp [apply.respMethods]
    · simp (config := {decide := true}) only [apply.reqFacts, ↓reduceIte]
      iunfold apply.mPre
      iframe; iexists x; iframe HR; ipureintro; exact hok x hs
    iunfold apply.mPost at Hpost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    join_ar
    fin_same
    itrivial
  have zLeaseCheckpoint : rq.leaseCheckpoint = none := nLC.1 (by simpa using Hif)
  wp_if_destruct
  · -- Alarm: the uber-applier's (`restoreAlarms` on an `ACTIVATE` or `DEACTIVATE`)
    have hl : lAl ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nAl.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HAl
    have hk : dispatchKind rq = .alarm := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, hs]
    wp_apply hAlarm $$ %E %p %opts %c %(GoInterface.ok ai) %lAl %x %log %Pre %Q %Post [Ha Hkv Hres Hc] as %resp %err ⟨Hpost, #HeI, %a', %c', Ha', #Hs', %hc'⟩
    · iframe HR Hu Hs Ha
      iunfold apply.mPre
      iframe
    iunfold apply.mPost at Hpost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    join_ar
    iframe Hres
    iexists a', c', (Outcome.applied log false)
    simp only [apply.Outcome.logAfter]
    iframe Ha' Hs' Hkv
    isplitl [HPP]
    · simp only [apply.cPost, ↓reduceIte]; iexact HPP
    isplitr
    · ipureintro
      refine ⟨by simp [apply.dispatchStep, hk, apply.preV3Kind, apply.storeKind, apply.Outcome.logAfter], ?_⟩
      rcases hc' with ⟨h1, -⟩ | h2
      · exact Or.inl h1
      · exact Or.inr ⟨rfl, hk, h2⟩
    simp only [apply.dispatchResult, hk, apply.preV3Kind, _root_.or_true, ↓reduceIte]
    iframe %hn
    iexists _
    iframe H0
    isplitl; rotate_left
    · first | iexact HeI | iapply applyErrIs_nil
    simp only [apply.dispatchAnswer, hk]
    itrivial
  have zAlarm : rq.alarm = none := nAl.1 (by simpa using Hif)
  wp_if_destruct
  · -- Authenticate
    have hl : lAu ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nAu.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HAu
    have hk : dispatchKind rq = .authenticate := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, hs]
    have hok := Hok.1
    simp only [rqOk, hk] at hok
    wp_apply HResp $$ %go!"Authenticate" %lAu %log %Pre %Q %Post [] [Hkv Hres Hc] as %resp %err ⟨Hpost, #HeI⟩
    · ipureintro; simp [apply.respMethods]
    · simp (config := {decide := true}) only [apply.reqFacts, ↓reduceIte]
      iunfold apply.mPre
      iframe; iexists x; iframe HR
    iunfold apply.mPost at Hpost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    join_ar
    fin_same
    itrivial
  have zAuthenticate : rq.authenticate = none := nAu.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthEnable
    have hl : lAE ≠ null := by simpa using Hif
    have hs : rq.authEnable = true := by
      cases h : rq.authEnable
      · exact absurd (nAE.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authEnable := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, hs]
    wp_apply HResp0 $$ %go!"AuthEnable" %log %Pre %Q %Post [] [Hkv Hres Hc] as %resp %err ⟨Hpost, #HeI⟩
    · ipureintro; simp [apply.resp0Methods]
    · iunfold apply.mPre
      iframe
    iunfold apply.mPost at Hpost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    join_ar
    fin_same
    itrivial
  have zAuthEnable : rq.authEnable = false := nAE.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthDisable
    have hl : lAD ≠ null := by simpa using Hif
    have hs : rq.authDisable = true := by
      cases h : rq.authDisable
      · exact absurd (nAD.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authDisable := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, hs]
    wp_apply HResp0 $$ %go!"AuthDisable" %log %Pre %Q %Post [] [Hkv Hres Hc] as %resp %err ⟨Hpost, #HeI⟩
    · ipureintro; simp [apply.resp0Methods]
    · iunfold apply.mPre
      iframe
    iunfold apply.mPost at Hpost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    join_ar
    fin_same
    itrivial
  have zAuthDisable : rq.authDisable = false := nAD.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthStatus
    have hl : lAS ≠ null := by simpa using Hif
    have hs : rq.authStatus = true := by
      cases h : rq.authStatus
      · exact absurd (nAS.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authStatus := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, hs]
    wp_apply HStatus $$ %log [Hkv Hres] as %resp %err ⟨Hkv, Hres, #HeI⟩
    · iframe
    join_ar
    ihave HPP : iprop(Post ∨ Pre) $$ [Hc]
    · iright; iapply apply.csContract_pre; iexact Hc
    fin_same
    itrivial
  have zAuthStatus : rq.authStatus = false := nAS.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthUserAdd
    have hl : lUA ≠ null := by simpa using Hif
    have hs : rq.authUserAdd = true := by
      cases h : rq.authUserAdd
      · exact absurd (nUA.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authUserAdd := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, hs]
    have hok := Hok.1
    simp only [rqOk, hk] at hok
    wp_apply HResp $$ %go!"UserAdd" %lUA %log %Pre %Q %Post [] [Hkv Hres Hc] as %resp %err ⟨Hpost, #HeI⟩
    · ipureintro; simp [apply.respMethods]
    · simp (config := {decide := true}) only [apply.reqFacts, ↓reduceIte]
      iunfold apply.mPre
      iframe
    iunfold apply.mPost at Hpost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    join_ar
    fin_same
    itrivial
  have zAuthUserAdd : rq.authUserAdd = false := nUA.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthUserDelete
    have hl : lUD ≠ null := by simpa using Hif
    have hs : rq.authUserDelete = true := by
      cases h : rq.authUserDelete
      · exact absurd (nUD.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authUserDelete := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, hs]
    have hok := Hok.1
    simp only [rqOk, hk] at hok
    wp_apply HResp $$ %go!"UserDelete" %lUD %log %Pre %Q %Post [] [Hkv Hres Hc] as %resp %err ⟨Hpost, #HeI⟩
    · ipureintro; simp [apply.respMethods]
    · simp (config := {decide := true}) only [apply.reqFacts, ↓reduceIte]
      iunfold apply.mPre
      iframe
    iunfold apply.mPost at Hpost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    join_ar
    fin_same
    itrivial
  have zAuthUserDelete : rq.authUserDelete = false := nUD.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthUserChangePassword
    have hl : lUC ≠ null := by simpa using Hif
    have hs : rq.authUserChangePassword = true := by
      cases h : rq.authUserChangePassword
      · exact absurd (nUC.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authUserChangePassword := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, hs]
    have hok := Hok.1
    simp only [rqOk, hk] at hok
    wp_apply HResp $$ %go!"UserChangePassword" %lUC %log %Pre %Q %Post [] [Hkv Hres Hc] as %resp %err ⟨Hpost, #HeI⟩
    · ipureintro; simp [apply.respMethods]
    · simp (config := {decide := true}) only [apply.reqFacts, ↓reduceIte]
      iunfold apply.mPre
      iframe
    iunfold apply.mPost at Hpost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    join_ar
    fin_same
    itrivial
  have zAuthUserChangePassword : rq.authUserChangePassword = false := nUC.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthUserGrantRole
    have hl : lUGR ≠ null := by simpa using Hif
    have hs : rq.authUserGrantRole = true := by
      cases h : rq.authUserGrantRole
      · exact absurd (nUGR.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authUserGrantRole := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, hs]
    have hok := Hok.1
    simp only [rqOk, hk] at hok
    wp_apply HResp $$ %go!"UserGrantRole" %lUGR %log %Pre %Q %Post [] [Hkv Hres Hc] as %resp %err ⟨Hpost, #HeI⟩
    · ipureintro; simp [apply.respMethods]
    · simp (config := {decide := true}) only [apply.reqFacts, ↓reduceIte]
      iunfold apply.mPre
      iframe
    iunfold apply.mPost at Hpost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    join_ar
    fin_same
    itrivial
  have zAuthUserGrantRole : rq.authUserGrantRole = false := nUGR.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthUserGet
    have hl : lUG ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nUG.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HUG
    have hk : dispatchKind rq = .authUserGet := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, zAuthUserGrantRole, hs]
    have hok := Hok.1
    simp only [rqOk, hk] at hok
    wp_apply HResp $$ %go!"UserGet" %lUG %log %Pre %Q %Post [] [Hkv Hres Hc] as %resp %err ⟨Hpost, #HeI⟩
    · ipureintro; simp [apply.respMethods]
    · simp (config := {decide := true}) only [apply.reqFacts, ↓reduceIte]
      iunfold apply.mPre
      iframe; iexists x; iframe HR
    iunfold apply.mPost at Hpost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    join_ar
    fin_same
    itrivial
  have zAuthUserGet : rq.authUserGet = none := nUG.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthUserRevokeRole
    have hl : lURR ≠ null := by simpa using Hif
    have hs : rq.authUserRevokeRole = true := by
      cases h : rq.authUserRevokeRole
      · exact absurd (nURR.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authUserRevokeRole := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, zAuthUserGrantRole, zAuthUserGet, hs]
    have hok := Hok.1
    simp only [rqOk, hk] at hok
    wp_apply HResp $$ %go!"UserRevokeRole" %lURR %log %Pre %Q %Post [] [Hkv Hres Hc] as %resp %err ⟨Hpost, #HeI⟩
    · ipureintro; simp [apply.respMethods]
    · simp (config := {decide := true}) only [apply.reqFacts, ↓reduceIte]
      iunfold apply.mPre
      iframe
    iunfold apply.mPost at Hpost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    join_ar
    fin_same
    itrivial
  have zAuthUserRevokeRole : rq.authUserRevokeRole = false := nURR.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthRoleAdd
    have hl : lRA ≠ null := by simpa using Hif
    have hs : rq.authRoleAdd = true := by
      cases h : rq.authRoleAdd
      · exact absurd (nRA.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authRoleAdd := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, zAuthUserGrantRole, zAuthUserGet, zAuthUserRevokeRole, hs]
    have hok := Hok.1
    simp only [rqOk, hk] at hok
    wp_apply HResp $$ %go!"RoleAdd" %lRA %log %Pre %Q %Post [] [Hkv Hres Hc] as %resp %err ⟨Hpost, #HeI⟩
    · ipureintro; simp [apply.respMethods]
    · simp (config := {decide := true}) only [apply.reqFacts, ↓reduceIte]
      iunfold apply.mPre
      iframe
    iunfold apply.mPost at Hpost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    join_ar
    fin_same
    itrivial
  have zAuthRoleAdd : rq.authRoleAdd = false := nRA.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthRoleGrantPermission
    have hl : lRGP ≠ null := by simpa using Hif
    have hs : rq.authRoleGrantPermission = true := by
      cases h : rq.authRoleGrantPermission
      · exact absurd (nRGP.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authRoleGrantPermission := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, zAuthUserGrantRole, zAuthUserGet, zAuthUserRevokeRole, zAuthRoleAdd, hs]
    have hok := Hok.1
    simp only [rqOk, hk] at hok
    wp_apply HResp $$ %go!"RoleGrantPermission" %lRGP %log %Pre %Q %Post [] [Hkv Hres Hc] as %resp %err ⟨Hpost, #HeI⟩
    · ipureintro; simp [apply.respMethods]
    · simp (config := {decide := true}) only [apply.reqFacts, ↓reduceIte]
      iunfold apply.mPre
      iframe
    iunfold apply.mPost at Hpost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    join_ar
    fin_same
    itrivial
  have zAuthRoleGrantPermission : rq.authRoleGrantPermission = false := nRGP.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthRoleGet
    have hl : lRG ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nRG.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HRG
    have hk : dispatchKind rq = .authRoleGet := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, zAuthUserGrantRole, zAuthUserGet, zAuthUserRevokeRole, zAuthRoleAdd, zAuthRoleGrantPermission, hs]
    have hok := Hok.1
    simp only [rqOk, hk] at hok
    wp_apply HResp $$ %go!"RoleGet" %lRG %log %Pre %Q %Post [] [Hkv Hres Hc] as %resp %err ⟨Hpost, #HeI⟩
    · ipureintro; simp [apply.respMethods]
    · simp (config := {decide := true}) only [apply.reqFacts, ↓reduceIte]
      iunfold apply.mPre
      iframe; iexists x; iframe HR
    iunfold apply.mPost at Hpost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    join_ar
    fin_same
    itrivial
  have zAuthRoleGet : rq.authRoleGet = none := nRG.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthRoleRevokePermission
    have hl : lRRP ≠ null := by simpa using Hif
    have hs : rq.authRoleRevokePermission = true := by
      cases h : rq.authRoleRevokePermission
      · exact absurd (nRRP.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authRoleRevokePermission := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, zAuthUserGrantRole, zAuthUserGet, zAuthUserRevokeRole, zAuthRoleAdd, zAuthRoleGrantPermission, zAuthRoleGet, hs]
    have hok := Hok.1
    simp only [rqOk, hk] at hok
    wp_apply HResp $$ %go!"RoleRevokePermission" %lRRP %log %Pre %Q %Post [] [Hkv Hres Hc] as %resp %err ⟨Hpost, #HeI⟩
    · ipureintro; simp [apply.respMethods]
    · simp (config := {decide := true}) only [apply.reqFacts, ↓reduceIte]
      iunfold apply.mPre
      iframe
    iunfold apply.mPost at Hpost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    join_ar
    fin_same
    itrivial
  have zAuthRoleRevokePermission : rq.authRoleRevokePermission = false := nRRP.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthRoleDelete
    have hl : lRD ≠ null := by simpa using Hif
    have hs : rq.authRoleDelete = true := by
      cases h : rq.authRoleDelete
      · exact absurd (nRD.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authRoleDelete := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, zAuthUserGrantRole, zAuthUserGet, zAuthUserRevokeRole, zAuthRoleAdd, zAuthRoleGrantPermission, zAuthRoleGet, zAuthRoleRevokePermission, hs]
    have hok := Hok.1
    simp only [rqOk, hk] at hok
    wp_apply HResp $$ %go!"RoleDelete" %lRD %log %Pre %Q %Post [] [Hkv Hres Hc] as %resp %err ⟨Hpost, #HeI⟩
    · ipureintro; simp [apply.respMethods]
    · simp (config := {decide := true}) only [apply.reqFacts, ↓reduceIte]
      iunfold apply.mPre
      iframe
    iunfold apply.mPost at Hpost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    join_ar
    fin_same
    itrivial
  have zAuthRoleDelete : rq.authRoleDelete = false := nRD.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthUserList
    have hl : lUL ≠ null := by simpa using Hif
    have hs : rq.authUserList = true := by
      cases h : rq.authUserList
      · exact absurd (nUL.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authUserList := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, zAuthUserGrantRole, zAuthUserGet, zAuthUserRevokeRole, zAuthRoleAdd, zAuthRoleGrantPermission, zAuthRoleGet, zAuthRoleRevokePermission, zAuthRoleDelete, hs]
    have hok := Hok.1
    simp only [rqOk, hk] at hok
    wp_apply HResp $$ %go!"UserList" %lUL %log %Pre %Q %Post [] [Hkv Hres Hc] as %resp %err ⟨Hpost, #HeI⟩
    · ipureintro; simp [apply.respMethods]
    · simp (config := {decide := true}) only [apply.reqFacts, ↓reduceIte]
      iunfold apply.mPre
      iframe
    iunfold apply.mPost at Hpost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    join_ar
    fin_same
    itrivial
  have zAuthUserList : rq.authUserList = false := nUL.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthRoleList
    have hl : lRL ≠ null := by simpa using Hif
    have hs : rq.authRoleList = true := by
      cases h : rq.authRoleList
      · exact absurd (nRL.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authRoleList := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, zAuthUserGrantRole, zAuthUserGet, zAuthUserRevokeRole, zAuthRoleAdd, zAuthRoleGrantPermission, zAuthRoleGet, zAuthRoleRevokePermission, zAuthRoleDelete, zAuthUserList, hs]
    have hok := Hok.1
    simp only [rqOk, hk] at hok
    wp_apply HResp $$ %go!"RoleList" %lRL %log %Pre %Q %Post [] [Hkv Hres Hc] as %resp %err ⟨Hpost, #HeI⟩
    · ipureintro; simp [apply.respMethods]
    · simp (config := {decide := true}) only [apply.reqFacts, ↓reduceIte]
      iunfold apply.mPre
      iframe
    iunfold apply.mPost at Hpost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    join_ar
    fin_same
    itrivial
  have zAuthRoleList : rq.authRoleList = false := nRL.1 (by simpa using Hif)
  -- `default`: `lg.Panic`: no field set, ruled out by the premise `dispatchOk`
  exfalso
  exact Hok.2.2 (by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, zAuthUserGrantRole, zAuthUserGet, zAuthUserRevokeRole, zAuthRoleAdd, zAuthRoleGrantPermission, zAuthRoleGet, zAuthRoleRevokePermission, zAuthRoleDelete, zAuthUserList, zAuthRoleList])
  -- after the join: `return ar` and the deferred metrics
  iintro Hj
  imod Hj with ⟨%resp, %err, %physc, %trace, %opS, a, r, ar, op, #H0, #HeI, Hpost⟩
  ihave #H0' := H0
  iStructNamed H0'
  dtail
  all_goals
    iapply HΦ
    iexact Hpost

end proof

end EtcdGrove
end Perennial
