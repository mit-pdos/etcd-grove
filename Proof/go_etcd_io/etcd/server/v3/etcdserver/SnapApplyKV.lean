/-
**The apply thread's applier state after `applySnapshot`** (D22 receiver epochs, S8d, step 4 of
`srvSnapApplied_of_walk`, `notes/snapshot-s8-plan.md`): `srvApplyKV` at the snapshot's environment
and the restored log.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyKVLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **Step 4: the applier state at the snapshot's environment** `E'` and the image's committed log
`A'` (strict M1, 2026-11-06: the store restored in place by `KV.Restore.contract`): the apply
thread's halves at the model's `(kvModelM on A', crevOf A')`, the store's open token and its
backend's whole share at the new backend `d'` (with its hook frozen at `g`, `hookIs`), the new
backend's facts, pool and reader token (`srvBeOwn`), the revisions' authority at a log no shorter
(`hxl`); with the new applier at `E'` (P6.2, 2026-11-03: `NewUberApplier`'s `uberIs`, until then the
wand with `E'`'s options) and the auth part by the mode at `E'` (`kvAuthM`; until then
`srvAuthApplyRes` at `E`); (the lease-expiry plan's S2–S4) the lessor's live set `L` with the apply
thread's half (`ltHalf`), and (step 2) the lessor's range deleter. Until strict M1 the watchable
store's sole writer at the restored physical names. (The mvcc merge, 2026-11-06: `lean`'s mode
and live set over strict M1's store; the deleter `lease.rdAt (mvcc.api.mvccLeases E.γ) E.s` restated at the API's
`mvccDeleter`.)
MERGE-TODO(snap-leases): strict M1 took `hnl : LogNoLease` (no live lease, `leasesKnown []`); with
`lean`'s live set `L` the KV's `leasesLive` needs `leasesKnown L` of the image's model (the image's
leases are `Recover`'s records). -/
theorem snap_applyKV (s : Loc) (γ : ApplyNames) (ci : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (π0 : ApplyPhys) (P : backend.BParams) (d' : mvcc.KBReal) (g : GoFunc)
    (up' : Loc) (opts' : apply.ApplierOptions) (w0 : GoInterface) (RD0 : IProp GF)
    (al ast lp cl : Loc) (x : apply.ApplyKV) (A' : List EntryModel) (L : List w64) (on : Bool)
    (st : auth.AuthState) (hxl : x.log.length ≤ (kvModelM on γr.kv A').length) :
    apply.uberIs (snapE E (snapγ γ π0 d'.γB) (metaTM d'.γB P) ci d' g d'.γB al ast lp cl d'.be) up' opts' ∗
      apply.uberOwn (snapE E (snapγ γ π0 d'.γB) (metaTM d'.γB P) ci d' g d'.γB al ast lp cl d'.be) up' (apply.alarmChain (snapE E (snapγ γ π0 d'.γB) (metaTM d'.γB P) ci d' g d'.γB al ast lp cl d'.be).authOn false false) ∗
      srvUberApplyAddr s ↦ (interface.mkOk apply.uberApplier.ty.PointerType #up' : GoInterface) ∗
      srvApi.wSt E.γs (kvModelM on γr.kv A') (crevOf γr.kv A') ∗ srvApi.crOwn E.γs (crevOf γr.kv A') ∗
      mvcc.api.mvccOpen E.γ ∗
      mvcc.api.mvccBackend E.γ 1 d' (batchLockInv (snapγ γ π0 d'.γB) (metaTM d'.γB P)) ∗
      backend.plHookRO d'.γB g ∗
      lease.leaseOwn (mvcc.api.mvccLeases E.γ) L ∅ ∗ lease.lessorRdOf (mvcc.api.mvccLeases E.γ) ∗
      lease.leaseRevokers (mvcc.api.mvccLeases E.γ) L ∗ apply.ltHalf E L ∗
      (∃ rd : GoFunc, lease.rdOwn (mvcc.api.mvccLeases E.γ) rd ∗ mvcc.api.mvccDeleter rd E.γ) ∗ E.RD ∗
      srvBeAddr s ↦{DFrac.own (1 : Qp).half} srvBeIface d'.be ∗
      dghostVar E.γbe (DFrac.own (1 : Qp).half.half) (bkKey d') ∗
      srvBeRO d' ∗ backend.bkRPool d'.γB d'.P d'.be ∗ apply.bkRT d' ∗
      revAuth E x.log ∗
      kvAuthM on s (snapE E (snapγ γ π0 d'.γB) (metaTM d'.γB P) ci d' g d'.γB al ast lp cl d'.be) (interface.mkOk apply.uberApplier.ty.PointerType #up' : GoInterface) st ∗
      srvWAddr s ↦□ w0 ∗
      waitOk w0 RD0 (fun ot id => waitRegdOpt ρ.wait id ot) (fun ot id => waitGoneOpt ρ.wait id ot) ∗
      RD0 ⊢
    |={⊤}=> ∃ x' : apply.ApplyKV,
      ⌜x'.log = kvModelM on γr.kv A' ∧ x'.chain = apply.alarmChain E.authOn false false ∧
        x'.crev = crevOf γr.kv A'⌝ ∗
      srvApplyKVM on s (snapE E (snapγ γ π0 d'.γB) (metaTM d'.γB P) ci d' g d'.γB al ast lp cl d'.be) ρ.wait x' st := by
  -- MERGE-TODO(walk): strict M1's body (mode off, no lease) below; `lean`'s `on`, `L`, `uberIs`,
  -- `kvAuthM` and the deleter to port
  iintro ⟨#Hub, Huo, Hua, HwSt, HcrO, HmO, HmB, #Hhk, Hlo, Hlr, Hrv, HLt, Hrdat, HRD, Hbe, Hγbe, #Hro,
    Hpl, Hrt, Hra, Hauar, #Hw, #Hwok, HRD0⟩
  ihave #Hlk := leasesKnown_noLease (GF := GF) _ hnl
  have hli : mvcc.leaseItemsOf (mvcc.stateAfter (kvModel γr.kv A')) = ∅ :=
    mvcc.leaseItemsOf_zero _ (mvcc.stateAfter_leaseZero _ hnl)
  imodintro
  iexists ⟨kvModelM on γr.kv A', apply.alarmChain E.authOn false false, crevOf γr.kv A'⟩
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl⟩
  iapply (srvApplyKVM_open _ _ _ _ _ _).2
  iexists _
  iframe Hua
  isplitr
  · iunfold apply.applierFor
    iexists up', opts'
    iframe Hub
    ipureintro; rfl
  isplitl [Huo HwSt HcrO HmO HmB Hlo Hlr Hrv HRD]
  · iunfold apply.applyKV
    iexists up'
    isplitr
    · ipureintro; rfl
    simp only [snapE_authOn]
    iframe Huo
    isplitl [HwSt HmB Hlo Hlr Hrv HRD]
    · iunfold apply.kvOwn
      simp only [snapE_γs, snapE_γ, snapE_RD]
      isplitl [HwSt]
      · iexists crevOf γr.kv A'; iexact HwSt
      isplitl [HmB]
      · iunfold apply.kvBk
        iexists d'
        dsimp only [snapE_γ, snapE_Pk, snapE_f, snapE_BkTie]
        iframe HmB
        rw [mvcc.api.etcdStorage_hookIs]
        iframe Hhk
        iunfold srvBkTie
        ipureintro; rfl
      iframe HRD
      iunfold apply.leasesLive
      iexists []
      iframe Hlk
      iunfold lease.lessorUser
      rw [hli]
      iframe Hlo Hlr Hrv
    iunfold apply.cmpOwn
    simp only [snapE_γs, snapE_γ]
    iframe HmO HcrO
  isplitl [Hbe Hγbe Hpl Hrt]
  · iunfold srvBeOwn
    iexists d'
    simp only [snapE_γbe, snapE_BkTie]
    iframe Hbe Hγbe Hro Hpl Hrt
  isplitl [Hra]
  · rw [revAuth_snapE]
    iunfold revAuth at Hra
    unfold revAuth
    icases Hra with ⟨%m, Hm, %hm⟩
    iexists m
    iframe Hm
    ipureintro
    intro k hk
    have h1 := hm k hk
    simp only at hxl ⊢
    omega
  isplitl [Hauar]
  · iexact Hauar
  isplitr [Hrdat]
  · iexists w0, RD0
    iframe Hw Hwok HRD0
  iExactEq Hrdat; simp

/-- **The auth part of the applier row at the snapshot's environment** (P6.2, 2026-11-03, F9):
from the walk's auth row (`snapAuthRowM`): off, the auth resource (it does not name the backend);
on, the base applier's auth layer at the new applier (`NewUberApplier`'s `uberIs`, its options'
auth store and lessor the server's) and the auth resource on the new backend at the image's state,
with the new environment's lenses of the store's half (`rwLens_authBeOn`, `roLends_authBeOn`). -/
theorem kvAuthM_snap (s : Loc) (γ : ApplyNames) (ci : Loc) (E : apply.AEnv GF) (π0 : ApplyPhys)
    (P : backend.BParams) (d' : mvcc.KBReal) (g : GoFunc) (up' : Loc) (opts' : apply.ApplierOptions) (al ast lp cl : Loc)
    (ua : GoInterface) (γr : ReadNames) (A' : List EntryModel) (hany : E.authMode ≠ .any)
    (hopts : opts'.AuthStore' = auth.authIface ast ∧ opts'.Lessor' = lease.lessorIface lp) :
    apply.uberIs (snapE E (snapγ γ π0 d'.γB) (metaTM d'.γB P) ci d' g d'.γB al ast lp cl d'.be) up' opts' ∗
      srvAuthStoreAddr s ↦□ auth.authIface ast ∗ srvLessorAddr s ↦□ lease.lessorIface lp ∗
      snapAuthRowM E.authMode s E ua ast γr A' d' (batchLockInv (snapγ γ π0 d'.γB) (metaTM d'.γB P)) g ⊢
    kvAuthM E.authOn s (snapE E (snapγ γ π0 d'.γB) (metaTM d'.γB P) ci d' g d'.γB al ast lp cl d'.be)
      (interface.mkOk apply.uberApplier.ty.PointerType #up' : GoInterface)
      (srvAuthAtLog γr.kv srvAuthSt0 A') := by
  iintro ⟨#Hub, #Hauf, #Hlef, Hrow⟩
  cases hM : E.authMode with
  | any => exact absurd hM hany
  | off =>
    have hon : E.authOn = false := by simp [apply.AEnv.authOn, hM]
    rw [hon]
    simp only [snapAuthRowM, kvAuthM]
    unfold srvAuthApplyRes
    simp only [snapE_authMode]
    try rw [hM]
    iexact Hrow
  | on γa =>
    have hon : E.authOn = true := by simp [apply.AEnv.authOn, hM, auth.AuthMode.isOn]
    rw [hon]
    simp only [snapAuthRowM, kvAuthM]
    icases Hrow with ⟨#Hub0, Hrow⟩
    iunfold srvUberBase at Hub0
    icases Hub0 with ⟨%au, %le, #Hauf0, #Hlef0, -, #Hlb, %stl, %Hau, #Hpub, #Hlat, #Hbd⟩
    icombine Hauf Hauf0 gives %e1
    icombine Hlef Hlef0 gives %e2
    subst e1 e2
    isplitr
    · iunfold srvUberBase
      iexists auth.authIface ast, lease.lessorIface lp
      iframe Hauf Hlef
      isplitr
      · iunfold apply.uberBaseAuth
        iexists up', opts'
        iframe Hub
        ipureintro; exact ⟨rfl, hopts.1, hopts.2⟩
      simp only [snapE_authMode, snapE_RD]
      try rw [hM]
      iframe Hlb
      iexists stl
      iframe Hpub Hlat Hbd
      ipureintro; exact Hau
    iunfold srvAuthApplyResB
    iexists ast, d'
    -- MERGE-TODO(walk): `srvAuthApplyResB`'s backend at the tie (`snapE_BkTie`), strict M1's
    simp only [snapE_authMode, snapE_P, snapE_f, snapE_RD, snapE_RW, snapE_RO]
    try rw [hM]
    iframe Hauf Hrow
    isplitr
    · iapply rwLens_authBeOn
    iapply roLends_authBeOn

end proof
end EtcdGrove
end Perennial
