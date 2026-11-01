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
- `waitOk`: `srvWAddr s ↦□ w0`, `waitOk w0 RD0 …`, `RD0` the hypotheses.
- (M2's apply side, A1, 2026-10-31) the compaction resources at `-1`: the new backend does not
  compact (`hcm'`), so they are free (`apply.cmpOwn_of_off`). -/
theorem snap_applyKV (s : Loc) (γ : ApplyNames) (ci : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (π0 : ApplyPhys) (γB : backend.BNames) (P : backend.BParams) (d' : mvcc.KBReal)
    (p' : mvcc.PhysNames) (γw : mvcc.WsNames) (ws : Loc) (g : GoFunc) (up' : Loc)
    (opts' : apply.ApplierOptions) (w0 : GoInterface) (RD0 : IProp GF) (al ast lp cl : Loc)
    (x : apply.ApplyKV) (R : mvcc.Log) (zal : Bool)
    (hγB : d'.γB = γB) (hkb' : p'.kb = some d') (hcm' : d'.cm = false) (hγw : γw.st = E.γ)
    (hwq : E.γ.watchQ = true)
    (hpre : x.log <+: [[], []] ++ R) (hRok : mvcc.restoreLogOk R)
    (hrbw : receiptBound GF ≤ backend.wbInit - 6) :
    apply.backendOptsOk (snapE E (snapγ γ π0 γB) (metaTM γB P) ci p' g γB al ast lp cl d'.be)
        opts' ∗
      mvcc.isWatchableStore ws E.s γw ∗
      (∀ E1 : apply.AEnv GF, ⌜E1.RD = E.RD⌝ -∗ apply.backendOptsOk E1 opts' -∗
        apply.uberIs E1 up' opts' ∗ ∃ ns cr, ⌜zal = true → ns = false ∧ cr = false⌝ ∗
          apply.uberOwn E1 up' (apply.alarmChain E1.authOn ns cr)) ∗
      srvUberApplyAddr s ↦ (interface.mkOk apply.uberApplier.ty.PointerType #up' : GoInterface) ∗
      mvcc.storeReader E.s E.γ ∗ mvcc.writerFrag (γw.st.withPhys p') ∗
      mvcc.watchWriter γw ([[], []] ++ R) ∗
      (mvcc.storeRT (γw.st.withPhys p') -∗ mvcc.writerOwn (γw.st.withPhys p')) ∗
      mvcc.bkRTx d'.γB d'.P d'.be ∗
      lease.leaseOwn E.γ.leases [] ∅ ∗ lease.lessorRdOf E.γ.leases ∗ lease.leaseRevokers E.γ.leases [] ∗ E.RD ∗
      srvBeAddr s ↦{DFrac.own (1 : Qp).half} srvBeIface d'.be ∗
      dghostVar E.γbe (DFrac.own (1 : Qp).half.half) d' ∗
      revAuth E x.log ∗ srvAuthApplyRes s E ∗
      srvWAddr s ↦□ w0 ∗
      waitOk w0 RD0 (fun ot id => waitRegdOpt ρ.wait id ot) (fun ot id => waitGoneOpt ρ.wait id ot) ∗
      RD0 ⊢
    |={⊤}=> ∃ x' : apply.ApplyKV,
      ⌜x'.log = [[], []] ++ R ∧ ∃ ns cr, x'.chain = apply.alarmChain E.authOn ns cr ∧
        (zal = true → ns = false ∧ cr = false)⌝ ∗
      srvApplyKV s (snapE E (snapγ γ π0 γB) (metaTM γB P) ci p' g γB al ast lp cl d'.be) ρ.wait x' := by
  have hrb : receiptBound GF ≤ 2 ^ 48 := by
    have : backend.wbInit = 2 ^ 40 - 1 := rfl
    omega
  iintro ⟨#Hopts, #Hws, Hube, Hua, Hrd, Hfrag, Hww, Hwo, Hrt, Hlo, Hlr, Hrv, HRD, Hbe, Hγbe, Hra, Hauar, #Hw,
    #Hwok, HRD0⟩
  ihave ⟨#Hub, %ns, %cr, %hz, Huo⟩ :=
    Hube $$ %(snapE E (snapγ γ π0 γB) (metaTM γB P) ci p' g γB al ast lp cl d'.be) %rfl Hopts
  ihave Hkv := kvOwn_snap E (snapγ γ π0 γB) (metaTM γB P) ci p' g γB al ast lp cl d' γw ws R hkb'
    hγw hwq hRok hrb $$ [Hws Hrd Hfrag Hww Hwo Hrt Hlo Hlr Hrv HRD]
  · iframe Hws Hrd Hfrag Hww Hwo Hrt Hlo Hlr Hrv HRD
  imodintro
  iexists ⟨[[], []] ++ R, apply.alarmChain E.authOn ns cr, -1⟩
  isplitr
  · ipureintro; exact ⟨rfl, ns, cr, rfl, hz⟩
  iunfold srvApplyKV
  iexists _
  iframe Hua
  isplitr
  · iunfold apply.applierFor
    iexists up', opts'
    iframe Hub
    ipureintro; rfl
  isplitl [Huo Hkv]
  · iunfold apply.applyKV
    iexists up'
    isplitr
    · ipureintro; rfl
    simp only [snapE_authOn]
    iframe Huo Hkv
    -- (M2's apply side, A1) the new backend does not compact: the compaction resources at `-1`
    iapply apply.cmpOwn_of_off
    simp [mvcc.kbCmpM, hkb', hcm']
  isplitl [Hbe Hγbe]
  · iunfold srvBeOwn
    iexists d'
    simp only [snapE_γbe]
    iframe Hbe Hγbe
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
  · iunfold srvAuthApplyRes at Hauar
    unfold srvAuthApplyRes
    simp only [snapE_authMode]
    iexact Hauar
  iexists w0, RD0
  iframe Hw Hwok HRD0

end proof
end EtcdGrove
end Perennial
