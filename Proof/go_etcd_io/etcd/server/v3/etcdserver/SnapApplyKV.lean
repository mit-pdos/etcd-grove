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

/-- **Step 4: the applier state at the snapshot's environment** `E'` and the restored log
`[[], []] ++ R`, with the new applier's chain (`alarmChain`, `NewUberApplier`'s: the open point of
the plan, `x'.chain`, is left to S-j1: the chain is stated as the walk gives it, which is all
`srvSnapApplied` needs, its `x'` being existential with only `x'.log` fixed).

Brief for the prover. Unfold `srvApplyKV` with `ua := mkOk up'`:
- `srvUberApplyAddr s ↦ ua` the hypothesis; `applierFor ua E'` and the chain: apply `Hube` at
  `E'` (`snapE_RD`: `⌜E'.RD = E.RD⌝` by `rfl`) and the step-3 `backendOptsOk E' opts'`; its
  `uberIs` gives `applierFor` (`iexists up', opts'`), its `uberOwn E' up' (alarmChain …)` the
  `applyKV`'s `uberOwn` (`x'.chain`).
- `kvOwn E' ([[], []] ++ R)`: `storeReader` (`storeReader_snapE`, `rfl`); `txn.kvWriter E.s E'.γ`
  as `BuildLemmas.lean:140` does at boot: `soleWriter` from `watchWriter`'s `idxCert` (of the
  logical names: equal at `E'.γ`) and tokens (`soleBudget = wBudget`: unfold both; `soleLog` of
  `[[], []] ++ R` from `hRok`'s non-empty revisions, see `txn.soleLog_boot` and `SoleWriter.lean`),
  `receiptBound GF ≤ 2 ^ 48` from `hrbw` and `backend.wbInit = 2 ^ 40 - 1`; `wlogOwn` by
  `txn.wlogOwn_watch` (`hwq`) at `{ γw with st := γw.st.withPhys p' }`
  (`mvcc.isWatchableStore_withPhys`, `hγw`) with `watchWriter`'s `wlog` half; `writerFrag` the
  hypothesis (`hγw`); `leasesLive`: `L := []`, `lessorUser = leaseOwn ∗ lessorRdOf` the hypotheses
  (leases of the logical names), `txn.leasesKnown [] (mvcc.stateAfter ([[], []] ++ R))` from `hRok`'s
  third conjunct (every restored put has lease `0`); `E'.RD = E.RD` the hypothesis; `writerOwn` from
  the wand applied to `mvcc.storeRT (γw.st.withPhys p')`, which is `bkRTx d'.γB d'.P d'.be`
  (`storeRT`/`kbRT` at `p'.kb = some d'`, `kbRT_some`).
- `srvBeOwn s E'`: `d'` (`snapE_kb hkb'`), the two hypotheses (`snapE_γbe`).
- `revAuth E' ([[], []] ++ R)` from `revAuth E x.log` (`revAuth_snapE`): the bound
  `uint.nat k < x.log.length ≤ ([[], []] ++ R).length` (`hpre.length_le`).
- `srvAuthApplyRes s E'`: the hypothesis (`snapE_authMode`; integration with the auth track's E2k).
- `waitOk`: `srvWAddr s ↦□ w0`, `waitOk w0 RD0 …`, `RD0` the hypotheses; (2026-11-04) the range
  deleter (`lease.rdAt`, of the logical names and the inner store, which `snapE` keeps) the hypothesis.
- (M2's item 15, stage B) the compaction resources at the restored revision `c'`, the caller's
  (until then at `-1`, free with the new backend not compacting, `apply.cmpOwn_of_off`).
- (2026-11-02, the backend-auth-split stage) `srvBeOwn`'s `srvBeRO d'` and the new backend's
  pool of readers (`backend.bkRPool`), from the walk. -/
theorem snap_applyKV (s : Loc) (γ : ApplyNames) (ci : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (π0 : ApplyPhys) (γB : backend.BNames) (P : backend.BParams) (d' : mvcc.KBReal)
    (p' : mvcc.PhysNames) (γw : mvcc.WsNames) (ws : Loc) (g : GoFunc) (up' : Loc)
    (opts' : apply.ApplierOptions) (w0 : GoInterface) (RD0 : IProp GF) (al ast lp cl : Loc)
    (x : apply.ApplyKV) (R : mvcc.Log)
    (hγB : d'.γB = γB) (hkb' : p'.kb = some d') (hγw : γw.st = E.γ)
    (hwq : E.γ.watchQ = true)
    (hpre : x.log <+: [[], []] ++ R) (hRok : mvcc.restoreLogOk R)
    (hrbw : receiptBound GF ≤ backend.wbInit - 6) (L : List w64) (c' : Int) (on : Bool)
    (st : auth.AuthState) :
    -- (P6.2, 2026-11-03) the new applier at `E'` (until then the wand `NewUberApplier` gives, with
    -- `E'`'s options), the auth part by the mode at `E'` (`kvAuthM`; until then `srvAuthApplyRes`
    -- at `E`)
    apply.uberIs (snapE E (snapγ γ π0 γB) (metaTM γB P) ci p' g γB al ast lp cl d'.be) up' opts' ∗
      mvcc.isWatchableStore ws E.s γw ∗
      apply.uberOwn (snapE E (snapγ γ π0 γB) (metaTM γB P) ci p' g γB al ast lp cl d'.be) up'
        (apply.alarmChain (snapE E (snapγ γ π0 γB) (metaTM γB P) ci p' g γB al ast lp cl d'.be).authOn
          false false) ∗
      srvUberApplyAddr s ↦ (interface.mkOk apply.uberApplier.ty.PointerType #up' : GoInterface) ∗
      mvcc.storeReader E.s E.γ ∗ mvcc.writerFrag (γw.st.withPhys p') ∗
      mvcc.watchWriter { γw with st := γw.st.withPhys p' } ([[], []] ++ R) ∗
      (mvcc.storeRT (γw.st.withPhys p') -∗ mvcc.writerOwn (γw.st.withPhys p')) ∗
      mvcc.bkRTx d'.γB d'.P d'.be ∗
      lease.leaseOwn E.γ.leases L ∅ ∗ lease.lessorRdOf E.γ.leases ∗ lease.leaseRevokers E.γ.leases L ∗
      apply.ltHalf E L ∗ lease.rdAt E.γ.leases E.s ∗ E.RD ∗
      srvBeAddr s ↦{DFrac.own (1 : Qp).half} srvBeIface d'.be ∗
      dghostVar E.γbe (DFrac.own (1 : Qp).half.half) d' ∗
      srvBeRO d' ∗ backend.bkRPool d'.γB d'.P d'.be ∗
      revAuth E x.log ∗
      kvAuthM on s (snapE E (snapγ γ π0 γB) (metaTM γB P) ci p' g γB al ast lp cl d'.be)
        (interface.mkOk apply.uberApplier.ty.PointerType #up' : GoInterface) st ∗
      srvWAddr s ↦□ w0 ∗
      waitOk w0 RD0 (fun ot id => waitRegdOpt ρ.wait id ot) (fun ot id => waitGoneOpt ρ.wait id ot) ∗
      RD0 ∗ apply.cmpOwn (snapE E (snapγ γ π0 γB) (metaTM γB P) ci p' g γB al ast lp cl d'.be) c' ⊢
    |={⊤}=> ∃ x' : apply.ApplyKV,
      ⌜x'.log = [[], []] ++ R ∧ x'.chain = apply.alarmChain E.authOn false false ∧ x'.crev = c'⌝ ∗
      srvApplyKVM on s (snapE E (snapγ γ π0 γB) (metaTM γB P) ci p' g γB al ast lp cl d'.be) ρ.wait x'
        st := by
  have hrb : receiptBound GF ≤ 2 ^ 48 := by
    have : backend.wbInit = 2 ^ 40 - 1 := rfl
    omega
  iintro ⟨#Hub, #Hws, Huo, Hua, Hrd, Hfrag, Hww, Hwo, Hrt, Hlo, Hlr, Hrv, HLt, Hrdat, HRD, Hbe, Hγbe, #Hro, Hpl, Hra, Hauar, #Hw,
    #Hwok, HRD0, Hcmp⟩
  ihave Hkv := kvOwn_snap E (snapγ γ π0 γB) (metaTM γB P) ci p' g γB al ast lp cl d' γw ws R hkb'
    hγw hwq hRok hrb L $$ [Hws Hrd Hfrag Hww Hwo Hrt Hlo Hlr Hrv HLt HRD]
  · iframe Hws Hrd Hfrag Hww Hwo Hrt Hlo Hlr Hrv HLt HRD
  imodintro
  iexists ⟨[[], []] ++ R, apply.alarmChain E.authOn false false, c'⟩
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
  isplitl [Huo Hkv Hcmp]
  · iunfold apply.applyKV
    iexists up'
    isplitr
    · ipureintro; rfl
    simp only [snapE_authOn]
    iframe Huo Hkv Hcmp
  isplitl [Hbe Hγbe Hpl]
  · iunfold srvBeOwn
    iexists d'
    simp only [snapE_γbe]
    iframe Hbe Hγbe Hro Hpl
    ipureintro; exact hkb'
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
    have h2 := hpre.length_le
    simp only at h2 ⊢
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
    (γB : backend.BNames) (P : backend.BParams) (d' : mvcc.KBReal) (p' : mvcc.PhysNames)
    (g : GoFunc) (up' : Loc) (opts' : apply.ApplierOptions) (al ast lp cl : Loc)
    (ua : GoInterface) (γr : ReadNames) (A' : List EntryModel) (hany : E.authMode ≠ .any)
    (hγB : d'.γB = γB) (hkb' : p'.kb = some d')
    (hopts : opts'.AuthStore' = auth.authIface ast ∧ opts'.Lessor' = lease.lessorIface lp) :
    apply.uberIs (snapE E (snapγ γ π0 γB) (metaTM γB P) ci p' g γB al ast lp cl d'.be) up' opts' ∗
      srvAuthStoreAddr s ↦□ auth.authIface ast ∗ srvLessorAddr s ↦□ lease.lessorIface lp ∗
      snapAuthRowM E.authMode s E ua ast γr A' d' (batchLockInv (snapγ γ π0 γB) (metaTM γB P)) g ⊢
    kvAuthM E.authOn s (snapE E (snapγ γ π0 γB) (metaTM γB P) ci p' g γB al ast lp cl d'.be)
      (interface.mkOk apply.uberApplier.ty.PointerType #up' : GoInterface)
      (srvAuthAtLog γr.kv srvAuthSt0 A') := by
  subst hγB
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
    isplitr
    · ipureintro; exact snapE_kb _ _ _ _ _ _ _ _ _ _ _ _ d' hkb'
    simp only [snapE_authMode, snapE_P, snapE_f, snapE_RD, snapE_RW, snapE_RO]
    try rw [hM]
    iframe Hauf Hrow
    isplitr
    · iapply rwLens_authBeOn
    iapply roLends_authBeOn

end proof
end EtcdGrove
end Perennial
