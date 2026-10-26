/-
**`dispatch` on an admitted admin request in the mode `on`** (the auth plan's E2n, 2026-10-26;
`notes/decisions.md`, "E2n of the auth plan"). Lean-first (no Rocq counterpart).

A second triple of `apply.uberApplier.dispatch` (`uber_applier.go`), beside its spec
(`Spec/.../apply/uberApplier__dispatch.lean`), for the requests the mode `on` admits by their shape
(`adminKindOk`: `SetUp`'s five, `UserAdd`, `RoleAdd`, `UserGrantRole`, `RoleGrantPermission`,
`AuthEnable`): with the current applier's admin triples (`applierAdmin E c a W`, E2m), the admin
side's authority with its fuel (`auth.authOwnFu γa hs`) and the store's write resource `W`, the
request's method runs on a time receipt the caller takes at a Go step of its own (`⧗ 1`, as
`srvWTPool_take_extra` pays for an entry), and its result (`AdminReq.result`: the model's step or its refusal, E2l's
`adminOutFu`) is the admin outcome of `dispatch`'s result (`adminDone`); without `shouldApplyV3`
nothing runs and the authority comes back. The KV, the chain's resources and the critical
section's contract are as for a request that leaves the log as it is (`fin_same` of the spec's
proof). The proof walks the same code as the spec's: every other request kind is ruled out by
`adminKindOk` at its branch.

Not here: its use at `uberApplier.Apply` and `applyEntryNormal` (the mode-on request path), the
current applier's admin triples at the apply thread (`uberOwn` after `restoreAlarms`), and the
borrow of the rest's half of `be` that `W` holds at the server ("E2n of the auth plan").
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier__dispatch
public import Spec.errors.Is
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.ApplySecObserve
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.WarnOfExpensiveRequest
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.WarnOfFailedRequest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.DispatchLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AdminChain
public import Proof.ReceiptTactics

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

/-- **The admin request a request model `rq` carries**, by the field `dispatch` takes
(`dispatchKind`): one of `SetUp`'s five, or none. -/
def apply.adminReqOf (rq : apply.IRRModel) : Option apply.AdminReq :=
  match apply.dispatchKind rq with
  | .authUserAdd => rq.authUserAdd.map (fun m => .userAdd m.name)
  | .authRoleAdd => rq.authRoleAdd.map .roleAdd
  | .authUserGrantRole => rq.authUserGrantRole.map (fun ur => .userGrantRole ur.1 ur.2)
  | .authRoleGrantPermission => rq.authRoleGrantPermission.map (fun nw => .roleGrantPermission nw.1 nw.2)
  | .authEnable => some .authEnable
  | _ => none

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The admin outcome of `dispatch`'s result `ar`** (the auth plan's E2n): with `v3`, the
request's result (`AdminReq.result` at the result's error: the step on the latest recorded state,
the authority with its fuel after it, or the model's refusal); without, the authority as it was. -/
def apply.adminDone (Own : auth.AuthNames → List auth.AuthState → IProp GF) (γa : auth.AuthNames) (M : auth.AuthMode)
    (hs : List auth.AuthState)
    (rq : apply.IRRModel) (v3 : Bool) (ar : Loc) : IProp GF :=
  if v3 then iprop(∃ (v : go_etcd_io.etcd.server.v3.etcdserver.apply.Result) (ad : apply.AdminReq), ⌜apply.adminReqOf rq = some ad⌝ ∗
    ar ↦□ v ∗ ad.result Own γa M hs v.Err')
  else Own γa hs

variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`a.dispatch(r, shouldApplyV3)` on an admitted admin request in the mode `on γa`** (see the
file header): `dispatch.spec`'s precondition but for the KV floor, the store's write token, the
rest buckets and the certificates (which an admin request does not use), with `adminKindOk rq` in
place of `rqOk`, the current applier's admin triples, the authority with its fuel, a time
receipt (the admin step's cost, E2l) and `W`. -/
abbrev apply.uberApplier.dispatch.adminSpec : Prop :=
  ∀ (E : apply.AEnv GF) (p : Loc) (opts : go_etcd_io.etcd.server.v3.etcdserver.apply.ApplierOptions) (c : apply.Chain) (a : GoInterface)
    (r : Loc) (rq : apply.IRRModel) (skip v3 : Bool) (log : mvcc.Log) (Pre Q Post : IProp GF)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (W : IProp GF) (γa : auth.AuthNames)
    (hs : List auth.AuthState) (Own : auth.AuthNames → List auth.AuthState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.uberIs E p opts ∗
      apply.irrWrapperIs r rq skip ∗ apply.chainRes c a info ∗
      structFieldRef uberApplier go!"applyV3" p ↦ a ∗ apply.applierSpec E c a ∗
      apply.applierAdmin E c a W Own ∗
      apply.kvOwn E log ∗ apply.cPre v3 E.P E.f Pre Q Post ∗
      ⌜E.authMode = .on γa ∧ apply.adminKindOk rq ∧ apply.dispatchOk E.authOn rq ∧
        receiptBound GF ≤ 2 ^ 48⌝ ∗ ⌜c.authOn = E.authOn⌝ ∗
      Own γa hs ∗ ⧗ 1 ∗ W }}
    (App (App (Val (p @!! go.GoType.PointerType uberApplier.ty @!! go!"dispatch")) (Val #r)) (Val #v3))
  {{ (ar : Loc), RET #ar; apply.chainResAny c a ∗ structFieldRef uberApplier go!"applyV3" p ↦ a ∗
      ∃ o : apply.Outcome, apply.kvOwn E (o.logAfter log) ∗ apply.cPost v3 Pre Post ∗
        ⌜apply.dispatchStep c rq v3 log o⌝ ∗ apply.resTrace ar ∗
        apply.dispatchResult rq v3 log skip ar o ∗ W ∗ apply.adminDone Own γa E.authMode hs rq v3 ar }}

end defs

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
  wp_apply hWER $$ [Hs1]
  · isplitr
    · ipureintro; exact HlgN
    iexists s1, _
    iframe Hs1
    ipureintro; exact ⟨rfl, Hipn⟩))

set_option hygiene false in
/-- The failure's warning (`WarnOfFailedRequest`), with a fresh stringer of the request. -/
local macro "wfr_step" : tactic => `(tactic| (
  wp_alloc s2 as Hs2
  wp_auto
  wp_apply hWFR $$ [Hs2]
  · isplitr
    · ipureintro; exact HlgN
    iexists s2, _
    iframe Hs2
    ipureintro; exact ⟨rfl, Hipn⟩))

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
  wp_apply hWER $$ [Hs1]
  · isplitr
    · ipureintro; exact HlgN
    iexists s1, _
    iframe Hs1
    ipureintro; exact ⟨rfl, Hipn⟩
  cases b <;> (try wp_auto) <;> (try wfr_step)))

set_option hygiene false in
/-- The deferred metrics, whatever `ar.Err`. -/
local macro "dtail" : tactic => `(tactic| (
  cases err <;> (try wp_auto) <;> first | ok_path | err_path))

set_option hygiene false in
/-- The postcondition for a request that leaves the KV and the chain as they are. -/
local macro "fin_same" : tactic => `(tactic| (
  (try ihave Hres := apply.chainResAny_of _ _ _ $$ Hres)
  iframe Hres
  iexists (GoInterface.ok ai), c, (Outcome.applied log false)
  simp only [apply.Outcome.logAfter]
  iframe Ha Hs Hkv
  isplitl [HPP]
  · simp only [apply.cPost, ↓reduceIte]; iexact HPP
  isplitr
  · ipureintro; simp [apply.kvFloorOk, apply.isFloorKind, apply.dispatchStep, apply.chainAfter, hk, apply.preV3Kind, apply.storeKind, apply.Outcome.logAfter]
  isplitl []
  · iintro %_; iapply (apply.chainClass_nonKV _ _ _ _ _ (by rw [hk]; rfl))
  first | isplitl [Htrc] | isplitl []
  · iapply apply.resTrace_of $$ H0
    first | iexact Htrc | iapply apply.traceRes_null
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
  (try ihave Hres := apply.chainResAny_of _ _ _ $$ Hres)
  iframe Hres
  iexists (GoInterface.ok ai), c, oc
  iframe Ha Hs Hkv
  isplitl [HPP]
  · simp only [apply.cPost, ↓reduceIte]; iexact HPP
  isplitr
  · ipureintro
    refine ⟨?_, Or.inl rfl, ?_⟩
    · simp only [apply.dispatchStep, hk, apply.preV3Kind, apply.storeKind,
        Bool.false_eq_true, _root_.or_self, ↓reduceIte]
      first | exact Hst.1 | exact Hst
    · first | exact fun _ _ => Hst.2 | simp [apply.kvFloorOk, apply.isFloorKind, hk]
  isplitl []
  · iintro %_; iexact Hcls
  first | isplitl [Htrc] | isplitl []
  · iapply apply.resTrace_of $$ H0
    first | iexact Htrc | iapply apply.traceRes_null
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


set_option linter.unusedVariables false in
set_option maxHeartbeats 10000000 in
/-- **`dispatch` on an admitted admin request** (see the file header). -/
theorem apply.uberApplier.dispatch.wp_admin
    (hIs : errors.Is.spec (GF := GF) (hG := hG))
    (hASO : txn.ApplySecObserve.spec (GF := GF) (hG := hG))
    (hWER : txn.WarnOfExpensiveRequest.spec (GF := GF) (hG := hG))
    (hWFR : txn.WarnOfFailedRequest.spec (GF := GF) (hG := hG)) :
    apply.uberApplier.dispatch.adminSpec (GF := GF) (hG := hG) := by
  intro E p opts c a r rq skip v3 log Pre Q Post info W γa hh Own
  wp_start as ⟨#Hu, #Hw, Hres, Ha, #Hs, #Hadm, Hkv, Hc, %Hok, %HcE, Hown, Hrc, HW⟩
  obtain ⟨Hmode, Hadmk, Hdok, Hrb⟩ := Hok
  ihave #Hu' := Hu
  iunfold apply.uberIs at Hu'
  icases Hu' with ⟨%Hpn, #Hopts, #Hlg, #Has, #Hwad, %base, #Hbase, #Hbs, -⟩
  ihave #Hopts' := Hopts
  iunfold apply.backendOptsOk at Hopts'
  icases Hopts' with ⟨%HlgN, -⟩
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
  ihave #HTx := apply.optReqIs_txnW lTx rq $$ HTx
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
  ihave %nUA := apply.optReqIs_null _ _ _ (apply.authUserAddIs_nn lUA) $$ HUA
  ihave %nUD := apply.presentIs_null _ _ $$ HUD
  ihave %nUC := apply.presentIs_null _ _ $$ HUC
  ihave %nUGR := apply.optReqIs_null _ _ _ (apply.authUserGrantRoleIs_nn lUGR) $$ HUGR
  ihave %nURR := apply.presentIs_null _ _ $$ HURR
  ihave %nUL := apply.presentIs_null _ _ $$ HUL
  ihave %nRL := apply.presentIs_null _ _ $$ HRL
  ihave %nRA := apply.optReqIs_null _ _ _ (apply.authRoleAddIs_nn lRA) $$ HRA
  ihave %nRD := apply.presentIs_null _ _ $$ HRD
  ihave %nRGP := apply.optReqIs_null _ _ _ (apply.authRoleGrantPermissionIs_nn lRGP) $$ HRGP
  ihave %nRRP := apply.presentIs_null _ _ $$ HRRP
  ihave %nDT := apply.presentIs_null _ _ $$ HDT
  ihave #Hsp := Hs
  iunfold apply.applierSpec at Hsp
  icases Hsp with ⟨%ai, %Hai, #Ht⟩
  subst Hai
  iunfold apply.applierAdmin at Hadm
  icases Hadm with ⟨%ai', %Hai', #Hat⟩
  injection Hai' with Hai'
  subst Hai'
  iunfold apply.adminTriples at Hat
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
  icases Hev' with ⟨-, -, -, -, -, #HCpl, -⟩
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
    exact absurd Hadmk (by simp [apply.adminKindOk, hk])
  have zClusterVersionSet : rq.clusterVersionSet = none := nCV.1 (by simpa using Hif)
  wp_if_destruct
  · -- ClusterMemberAttrSet
    have hl : lCM ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nCM.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HCM
    have hk : dispatchKind rq = .clusterMemberAttrSet := by simp [dispatchKind, zClusterVersionSet, hs]
    exact absurd Hadmk (by simp [apply.adminKindOk, hk])
  have zClusterMemberAttrSet : rq.clusterMemberAttrSet = none := nCM.1 (by simpa using Hif)
  wp_if_destruct
  · -- DowngradeInfoSet (D22, 2026-10-23: not admitted, `rqOk`)
    have hl : lDI ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nDI.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HDI
    have hk : dispatchKind rq = .downgradeInfoSet := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, hs]
    exact absurd Hadmk (by simp [apply.adminKindOk, hk])
  have zDowngradeInfoSet : rq.downgradeInfoSet = none := nDI.1 (by simpa using Hif)
  wp_if_destruct
  · -- DowngradeVersionTest: nothing
    have hl : lDT ≠ null := by simpa using Hif
    have hs : rq.downgradeVersionTest = true := by
      cases h : rq.downgradeVersionTest
      · exact absurd (nDT.2 h) hl
      · rfl
    have hk : dispatchKind rq = .downgradeVersionTest := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, hs]
    exact absurd Hadmk (by simp [apply.adminKindOk, hk])
  have zDowngradeVersionTest : rq.downgradeVersionTest = false := nDT.1 (by simpa using Hif)
  have hpre : apply.preV3Kind (dispatchKind rq) = false :=
    apply.preV3Kind_dispatchKind rq zClusterVersionSet zClusterMemberAttrSet zDowngradeInfoSet zDowngradeVersionTest
  cases v3
  · -- not `shouldApplyV3`: nil, the authority back
    (try wp_auto)
    ok_path
    iapply HΦ
    ihave Hres := apply.chainResAny_of _ _ _ $$ Hres
    iframe Hres Ha HW
    iexists (Outcome.applied log false)
    simp only [apply.Outcome.logAfter]
    iframe Hkv
    isplitl [Hc]
    · simp only [apply.cPost, apply.cPre, Bool.false_eq_true, ↓reduceIte]; iexact Hc
    isplitr
    · ipureintro; simp [apply.dispatchStep, hpre]
    isplitl []
    · iapply apply.resTrace_null
    isplitl []
    · simp only [apply.dispatchResult, hpre, Bool.false_eq_true, or_self, ↓reduceIte]; ipureintro; trivial
    simp only [apply.adminDone, Bool.false_eq_true, ↓reduceIte]
    iexact Hown
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
      (apply.chainResAny c (GoInterface.ok ai) ∗ structFieldRef uberApplier go!"applyV3" p ↦ GoInterface.ok ai ∗
        ∃ o : apply.Outcome, apply.kvOwn E (o.logAfter log) ∗ apply.cPost true Pre Post ∗
          ⌜apply.dispatchStep c rq true log o⌝ ∗ apply.resTrace «$r0_ptr» ∗
          apply.dispatchResult rq true log skip «$r0_ptr» o ∗ W ∗
          apply.adminDone Own γa E.authMode hh rq true «$r0_ptr»))
    with [a r ar op «$r0» Hc Hres Ha Hkv Hown Hrc HW]
  · -- Range
    have hl : lRa ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nRa.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HRa
    have hk : dispatchKind rq = .range := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, hs]
    exact absurd Hadmk (by simp [apply.adminKindOk, hk])
  have zRange : rq.range = none := nRa.1 (by simpa using Hif)
  wp_if_destruct
  · -- Put
    have hl : lPu ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nPu.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HPu
    have hk : dispatchKind rq = .put := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, hs]
    exact absurd Hadmk (by simp [apply.adminKindOk, hk])
  have zPut : rq.put = none := nPu.1 (by simpa using Hif)
  wp_if_destruct
  · -- DeleteRange
    have hl : lDe ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nDe.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HDe
    have hk : dispatchKind rq = .deleteRange := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, hs]
    exact absurd Hadmk (by simp [apply.adminKindOk, hk])
  have zDeleteRange : rq.deleteRange = none := nDe.1 (by simpa using Hif)
  wp_if_destruct
  · -- Txn
    have hl : lTx ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nTx.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HTx
    have hk : dispatchKind rq = .txn := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, hs]
    exact absurd Hadmk (by simp [apply.adminKindOk, hk])
  have zTxn : rq.txn = none := nTx.1 (by simpa using Hif)
  wp_if_destruct
  · -- Compaction: out of the model (the premise `dispatchOk`)
    have hl : lCo ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nCo.2 h))
    have hk : dispatchKind rq = .compaction := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, hs]
    exact absurd Hadmk (by simp [apply.adminKindOk, hk])
  have zCompaction : rq.compaction = none := nCo.1 (by simpa using Hif)
  wp_if_destruct
  · -- LeaseGrant
    have hl : lLG ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nLG.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HLG
    have hk : dispatchKind rq = .leaseGrant := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, hs]
    exact absurd Hadmk (by simp [apply.adminKindOk, hk])
  have zLeaseGrant : rq.leaseGrant = none := nLG.1 (by simpa using Hif)
  wp_if_destruct
  · -- LeaseRevoke
    have hl : lLR ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nLR.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HLR
    have hk : dispatchKind rq = .leaseRevoke := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, hs]
    exact absurd Hadmk (by simp [apply.adminKindOk, hk])
  have zLeaseRevoke : rq.leaseRevoke = none := nLR.1 (by simpa using Hif)
  wp_if_destruct
  · -- LeaseCheckpoint
    have hl : lLC ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nLC.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HLC
    have hk : dispatchKind rq = .leaseCheckpoint := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, hs]
    exact absurd Hadmk (by simp [apply.adminKindOk, hk])
  have zLeaseCheckpoint : rq.leaseCheckpoint = none := nLC.1 (by simpa using Hif)
  wp_if_destruct
  · -- Alarm: not admitted (`rqOk`; D22, 2026-10-23: its writer takes `AEnv.RW`)
    have hl : lAl ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nAl.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HAl
    have hk : dispatchKind rq = .alarm := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, hs]
    exact absurd Hadmk (by simp [apply.adminKindOk, hk])
  have zAlarm : rq.alarm = none := nAl.1 (by simpa using Hif)
  wp_if_destruct
  · -- Authenticate (D22, 2026-10-23: not admitted, `rqOk`)
    have hl : lAu ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nAu.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HAu
    have hk : dispatchKind rq = .authenticate := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, hs]
    exact absurd Hadmk (by simp [apply.adminKindOk, hk])
  have zAuthenticate : rq.authenticate = none := nAu.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthEnable (the auth plan's E2n: admitted in the mode `on`)
    have hl : lAE ≠ null := by simpa using Hif
    have hs : rq.authEnable = true := by
      cases h : rq.authEnable
      · exact absurd (nAE.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authEnable := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, hs]
    have hnm : apply.AdminReq.authEnable.nameOk := trivial
    wp_apply Hat $$ %apply.AdminReq.authEnable %(null : Loc) %γa %hh %log %Pre %Q %Post %info [] [Hown Hrc HW Hkv Hres Hc] as %resp %err ⟨Hpost, #HeI, HW, Hdone⟩
    · ipureintro; exact ⟨Hmode, Hrb, hnm⟩
    · iunfold apply.AdminReq.reqIs
      iunfold apply.mPre
      iframe
      (try dsimp only)
      (try iunfold auth.roleAddReqIs)
      (try iexact HR)
      (try itrivial)
    iunfold apply.mPost at Hpost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    join_ar
    iframe Hres Ha HW
    iexists (Outcome.applied log false)
    simp only [apply.Outcome.logAfter]
    iframe Hkv
    isplitl [HPP]
    · simp only [apply.cPost, ↓reduceIte]; iexact HPP
    isplitr
    · ipureintro; simp [apply.dispatchStep, hk, apply.preV3Kind, apply.storeKind, apply.Outcome.logAfter]
    isplitl []
    · iapply apply.resTrace_of $$ H0
      iapply apply.traceRes_null
    isplitl []
    · simp only [apply.dispatchResult, hk, apply.preV3Kind, _root_.or_true, ↓reduceIte]
      iframe %hn
      iexists _
      iframe H0
      isplitl; rotate_left
      · iexact HeI
      simp only [apply.dispatchAnswer, hk]
      try itrivial
    simp only [apply.adminDone, ↓reduceIte]
    iexists _, apply.AdminReq.authEnable
    iframe H0
    isplitr
    · ipureintro; simp [apply.adminReqOf, hk, hs]
    iexact Hdone
  have zAuthEnable : rq.authEnable = false := nAE.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthDisable (D22, 2026-10-23: not admitted, `rqOk`)
    have hl : lAD ≠ null := by simpa using Hif
    have hs : rq.authDisable = true := by
      cases h : rq.authDisable
      · exact absurd (nAD.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authDisable := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, hs]
    exact absurd Hadmk (by simp [apply.adminKindOk, hk])
  have zAuthDisable : rq.authDisable = false := nAD.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthStatus
    have hl : lAS ≠ null := by simpa using Hif
    have hs : rq.authStatus = true := by
      cases h : rq.authStatus
      · exact absurd (nAS.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authStatus := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, hs]
    exact absurd Hadmk (by simp [apply.adminKindOk, hk])
  have zAuthStatus : rq.authStatus = false := nAS.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthUserAdd (the auth plan's E2n: admitted in the mode `on`)
    have hl : lUA ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nUA.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HUA
    have hk : dispatchKind rq = .authUserAdd := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, hs]
    have hns : (apply.AdminReq.userAdd x.name).nameOk ∧ x.pwSure := by
      have h := Hadmk; simp only [apply.adminKindOk, hk] at h
      exact h x hs
    have hnm := hns.1
    ihave #HS := apply.authUserAddIs_sure _ _ hns.2 $$ HR
    ihave #HR := apply.authUserAddIs_req _ _ $$ HR
    wp_apply Hat $$ %(apply.AdminReq.userAdd x.name) %lUA %γa %hh %log %Pre %Q %Post %info [] [HR Hown Hrc HW Hkv Hres Hc] as %resp %err ⟨Hpost, #HeI, HW, Hdone⟩
    · ipureintro; exact ⟨Hmode, Hrb, hnm⟩
    · iunfold apply.AdminReq.reqIs
      iunfold apply.mPre
      iframe
      (try dsimp only)
      (try iframe HR HS)
      (try iunfold auth.roleAddReqIs)
      (try iexact HR)
      (try itrivial)
    iunfold apply.mPost at Hpost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    join_ar
    iframe Hres Ha HW
    iexists (Outcome.applied log false)
    simp only [apply.Outcome.logAfter]
    iframe Hkv
    isplitl [HPP]
    · simp only [apply.cPost, ↓reduceIte]; iexact HPP
    isplitr
    · ipureintro; simp [apply.dispatchStep, hk, apply.preV3Kind, apply.storeKind, apply.Outcome.logAfter]
    isplitl []
    · iapply apply.resTrace_of $$ H0
      iapply apply.traceRes_null
    isplitl []
    · simp only [apply.dispatchResult, hk, apply.preV3Kind, _root_.or_true, ↓reduceIte]
      iframe %hn
      iexists _
      iframe H0
      isplitl; rotate_left
      · iexact HeI
      simp only [apply.dispatchAnswer, hk]
      try itrivial
    simp only [apply.adminDone, ↓reduceIte]
    iexists _, (apply.AdminReq.userAdd x.name)
    iframe H0
    isplitr
    · ipureintro; simp [apply.adminReqOf, hk, hs]
    iexact Hdone
  have zAuthUserAdd : rq.authUserAdd = none := nUA.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthUserDelete (D22, 2026-10-23: not admitted, `rqOk`)
    have hl : lUD ≠ null := by simpa using Hif
    have hs : rq.authUserDelete = true := by
      cases h : rq.authUserDelete
      · exact absurd (nUD.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authUserDelete := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, hs]
    exact absurd Hadmk (by simp [apply.adminKindOk, hk])
  have zAuthUserDelete : rq.authUserDelete = false := nUD.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthUserChangePassword (D22, 2026-10-23: not admitted, `rqOk`)
    have hl : lUC ≠ null := by simpa using Hif
    have hs : rq.authUserChangePassword = true := by
      cases h : rq.authUserChangePassword
      · exact absurd (nUC.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authUserChangePassword := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, hs]
    exact absurd Hadmk (by simp [apply.adminKindOk, hk])
  have zAuthUserChangePassword : rq.authUserChangePassword = false := nUC.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthUserGrantRole (the auth plan's E2n: admitted in the mode `on`)
    have hl : lUGR ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nUGR.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HUGR
    have hk : dispatchKind rq = .authUserGrantRole := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, hs]
    have hnm : (apply.AdminReq.userGrantRole x.1 x.2).nameOk := by
      have h := Hadmk; simp only [apply.adminKindOk, hk] at h
      first | exact h x hs | exact h x.1 x.2 hs
    iunfold apply.authUserGrantRoleIs at HR
    wp_apply Hat $$ %(apply.AdminReq.userGrantRole x.1 x.2) %lUGR %γa %hh %log %Pre %Q %Post %info [] [HR Hown Hrc HW Hkv Hres Hc] as %resp %err ⟨Hpost, #HeI, HW, Hdone⟩
    · ipureintro; exact ⟨Hmode, Hrb, hnm⟩
    · iunfold apply.AdminReq.reqIs
      iunfold apply.mPre
      iframe
      (try dsimp only)
      (try iunfold auth.roleAddReqIs)
      (try iexact HR)
      (try itrivial)
    iunfold apply.mPost at Hpost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    join_ar
    iframe Hres Ha HW
    iexists (Outcome.applied log false)
    simp only [apply.Outcome.logAfter]
    iframe Hkv
    isplitl [HPP]
    · simp only [apply.cPost, ↓reduceIte]; iexact HPP
    isplitr
    · ipureintro; simp [apply.dispatchStep, hk, apply.preV3Kind, apply.storeKind, apply.Outcome.logAfter]
    isplitl []
    · iapply apply.resTrace_of $$ H0
      iapply apply.traceRes_null
    isplitl []
    · simp only [apply.dispatchResult, hk, apply.preV3Kind, _root_.or_true, ↓reduceIte]
      iframe %hn
      iexists _
      iframe H0
      isplitl; rotate_left
      · iexact HeI
      simp only [apply.dispatchAnswer, hk]
      try itrivial
    simp only [apply.adminDone, ↓reduceIte]
    iexists _, (apply.AdminReq.userGrantRole x.1 x.2)
    iframe H0
    isplitr
    · ipureintro; simp [apply.adminReqOf, hk, hs]
    iexact Hdone
  have zAuthUserGrantRole : rq.authUserGrantRole = none := nUGR.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthUserGet (D22, 2026-10-23: not admitted, `rqOk`)
    have hl : lUG ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nUG.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HUG
    have hk : dispatchKind rq = .authUserGet := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, zAuthUserGrantRole, hs]
    exact absurd Hadmk (by simp [apply.adminKindOk, hk])
  have zAuthUserGet : rq.authUserGet = none := nUG.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthUserRevokeRole (D22, 2026-10-23: not admitted, `rqOk`)
    have hl : lURR ≠ null := by simpa using Hif
    have hs : rq.authUserRevokeRole = true := by
      cases h : rq.authUserRevokeRole
      · exact absurd (nURR.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authUserRevokeRole := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, zAuthUserGrantRole, zAuthUserGet, hs]
    exact absurd Hadmk (by simp [apply.adminKindOk, hk])
  have zAuthUserRevokeRole : rq.authUserRevokeRole = false := nURR.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthRoleAdd (the auth plan's E2n: admitted in the mode `on`)
    have hl : lRA ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nRA.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HRA
    have hk : dispatchKind rq = .authRoleAdd := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, zAuthUserGrantRole, zAuthUserGet, zAuthUserRevokeRole, hs]
    have hnm : (apply.AdminReq.roleAdd x).nameOk := by
      have h := Hadmk; simp only [apply.adminKindOk, hk] at h
      first | exact h x hs | exact h x.1 x.2 hs
    iunfold apply.authRoleAddIs at HR
    wp_apply Hat $$ %(apply.AdminReq.roleAdd x) %lRA %γa %hh %log %Pre %Q %Post %info [] [HR Hown Hrc HW Hkv Hres Hc] as %resp %err ⟨Hpost, #HeI, HW, Hdone⟩
    · ipureintro; exact ⟨Hmode, Hrb, hnm⟩
    · iunfold apply.AdminReq.reqIs
      iunfold apply.mPre
      iframe
      (try dsimp only)
      (try iunfold auth.roleAddReqIs)
      (try iexact HR)
      (try itrivial)
    iunfold apply.mPost at Hpost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    join_ar
    iframe Hres Ha HW
    iexists (Outcome.applied log false)
    simp only [apply.Outcome.logAfter]
    iframe Hkv
    isplitl [HPP]
    · simp only [apply.cPost, ↓reduceIte]; iexact HPP
    isplitr
    · ipureintro; simp [apply.dispatchStep, hk, apply.preV3Kind, apply.storeKind, apply.Outcome.logAfter]
    isplitl []
    · iapply apply.resTrace_of $$ H0
      iapply apply.traceRes_null
    isplitl []
    · simp only [apply.dispatchResult, hk, apply.preV3Kind, _root_.or_true, ↓reduceIte]
      iframe %hn
      iexists _
      iframe H0
      isplitl; rotate_left
      · iexact HeI
      simp only [apply.dispatchAnswer, hk]
      try itrivial
    simp only [apply.adminDone, ↓reduceIte]
    iexists _, (apply.AdminReq.roleAdd x)
    iframe H0
    isplitr
    · ipureintro; simp [apply.adminReqOf, hk, hs]
    iexact Hdone
  have zAuthRoleAdd : rq.authRoleAdd = none := nRA.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthRoleGrantPermission (the auth plan's E2n: admitted in the mode `on`)
    have hl : lRGP ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nRGP.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HRGP
    have hk : dispatchKind rq = .authRoleGrantPermission := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, zAuthUserGrantRole, zAuthUserGet, zAuthUserRevokeRole, zAuthRoleAdd, hs]
    have hnm : (apply.AdminReq.roleGrantPermission x.1 x.2).nameOk := by
      have h := Hadmk; simp only [apply.adminKindOk, hk] at h
      first | exact h x hs | exact h x.1 x.2 hs
    iunfold apply.authRoleGrantPermissionIs at HR
    wp_apply Hat $$ %(apply.AdminReq.roleGrantPermission x.1 x.2) %lRGP %γa %hh %log %Pre %Q %Post %info [] [HR Hown Hrc HW Hkv Hres Hc] as %resp %err ⟨Hpost, #HeI, HW, Hdone⟩
    · ipureintro; exact ⟨Hmode, Hrb, hnm⟩
    · iunfold apply.AdminReq.reqIs
      iunfold apply.mPre
      iframe
      (try dsimp only)
      (try iunfold auth.roleAddReqIs)
      (try iexact HR)
      (try itrivial)
    iunfold apply.mPost at Hpost
    icases Hpost with ⟨Hkv, Hres, HPP⟩
    join_ar
    iframe Hres Ha HW
    iexists (Outcome.applied log false)
    simp only [apply.Outcome.logAfter]
    iframe Hkv
    isplitl [HPP]
    · simp only [apply.cPost, ↓reduceIte]; iexact HPP
    isplitr
    · ipureintro; simp [apply.dispatchStep, hk, apply.preV3Kind, apply.storeKind, apply.Outcome.logAfter]
    isplitl []
    · iapply apply.resTrace_of $$ H0
      iapply apply.traceRes_null
    isplitl []
    · simp only [apply.dispatchResult, hk, apply.preV3Kind, _root_.or_true, ↓reduceIte]
      iframe %hn
      iexists _
      iframe H0
      isplitl; rotate_left
      · iexact HeI
      simp only [apply.dispatchAnswer, hk]
      try itrivial
    simp only [apply.adminDone, ↓reduceIte]
    iexists _, (apply.AdminReq.roleGrantPermission x.1 x.2)
    iframe H0
    isplitr
    · ipureintro; simp [apply.adminReqOf, hk, hs]
    iexact Hdone
  have zAuthRoleGrantPermission : rq.authRoleGrantPermission = none := nRGP.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthRoleGet (D22, 2026-10-23: not admitted, `rqOk`)
    have hl : lRG ≠ null := by simpa using Hif
    obtain ⟨x, hs⟩ := Option.ne_none_iff_exists'.mp (fun h => hl (nRG.2 h))
    ihave #HR := apply.optReqIs_some _ _ _ _ hs $$ HRG
    have hk : dispatchKind rq = .authRoleGet := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, zAuthUserGrantRole, zAuthUserGet, zAuthUserRevokeRole, zAuthRoleAdd, zAuthRoleGrantPermission, hs]
    exact absurd Hadmk (by simp [apply.adminKindOk, hk])
  have zAuthRoleGet : rq.authRoleGet = none := nRG.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthRoleRevokePermission (D22, 2026-10-23: not admitted, `rqOk`)
    have hl : lRRP ≠ null := by simpa using Hif
    have hs : rq.authRoleRevokePermission = true := by
      cases h : rq.authRoleRevokePermission
      · exact absurd (nRRP.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authRoleRevokePermission := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, zAuthUserGrantRole, zAuthUserGet, zAuthUserRevokeRole, zAuthRoleAdd, zAuthRoleGrantPermission, zAuthRoleGet, hs]
    exact absurd Hadmk (by simp [apply.adminKindOk, hk])
  have zAuthRoleRevokePermission : rq.authRoleRevokePermission = false := nRRP.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthRoleDelete (D22, 2026-10-23: not admitted, `rqOk`)
    have hl : lRD ≠ null := by simpa using Hif
    have hs : rq.authRoleDelete = true := by
      cases h : rq.authRoleDelete
      · exact absurd (nRD.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authRoleDelete := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, zAuthUserGrantRole, zAuthUserGet, zAuthUserRevokeRole, zAuthRoleAdd, zAuthRoleGrantPermission, zAuthRoleGet, zAuthRoleRevokePermission, hs]
    exact absurd Hadmk (by simp [apply.adminKindOk, hk])
  have zAuthRoleDelete : rq.authRoleDelete = false := nRD.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthUserList (D22, 2026-10-23: not admitted, `rqOk`)
    have hl : lUL ≠ null := by simpa using Hif
    have hs : rq.authUserList = true := by
      cases h : rq.authUserList
      · exact absurd (nUL.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authUserList := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, zAuthUserGrantRole, zAuthUserGet, zAuthUserRevokeRole, zAuthRoleAdd, zAuthRoleGrantPermission, zAuthRoleGet, zAuthRoleRevokePermission, zAuthRoleDelete, hs]
    exact absurd Hadmk (by simp [apply.adminKindOk, hk])
  have zAuthUserList : rq.authUserList = false := nUL.1 (by simpa using Hif)
  wp_if_destruct
  · -- AuthRoleList (D22, 2026-10-23: not admitted, `rqOk`)
    have hl : lRL ≠ null := by simpa using Hif
    have hs : rq.authRoleList = true := by
      cases h : rq.authRoleList
      · exact absurd (nRL.2 h) hl
      · rfl
    have hk : dispatchKind rq = .authRoleList := by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, zAuthUserGrantRole, zAuthUserGet, zAuthUserRevokeRole, zAuthRoleAdd, zAuthRoleGrantPermission, zAuthRoleGet, zAuthRoleRevokePermission, zAuthRoleDelete, zAuthUserList, hs]
    exact absurd Hadmk (by simp [apply.adminKindOk, hk])
  have zAuthRoleList : rq.authRoleList = false := nRL.1 (by simpa using Hif)
  -- `default`: `lg.Panic`: no field set, ruled out by the premise `dispatchOk`
  exfalso
  exact Hdok.2.1 (by simp [dispatchKind, zClusterVersionSet, zClusterMemberAttrSet, zDowngradeInfoSet, zDowngradeVersionTest, zRange, zPut, zDeleteRange, zTxn, zCompaction, zLeaseGrant, zLeaseRevoke, zLeaseCheckpoint, zAlarm, zAuthenticate, zAuthEnable, zAuthDisable, zAuthStatus, zAuthUserAdd, zAuthUserDelete, zAuthUserChangePassword, zAuthUserGrantRole, zAuthUserGet, zAuthUserRevokeRole, zAuthRoleAdd, zAuthRoleGrantPermission, zAuthRoleGet, zAuthRoleRevokePermission, zAuthRoleDelete, zAuthUserList, zAuthRoleList])
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
