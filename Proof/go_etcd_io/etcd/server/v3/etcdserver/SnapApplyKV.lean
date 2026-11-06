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
thread's halves at the model's `(kvModel A', crevOf A')`, the store's open token and its backend's
whole share at the new backend `d'` (with its hook frozen at `g`, `hookIs`), no lease live (the
image's history puts none, `hnl`), the new backend's facts, pool and reader token (`srvBeOwn`), the
revisions' authority at a log no shorter (`hxl`); with the new applier's chain (`NewUberApplier`'s).
Until then the watchable store's sole writer at the restored physical names. -/
theorem snap_applyKV (s : Loc) (γ : ApplyNames) (ci : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (π0 : ApplyPhys) (P : backend.BParams) (d' : mvcc.KBReal) (g : GoFunc)
    (up' : Loc) (opts' : apply.ApplierOptions) (w0 : GoInterface) (RD0 : IProp GF)
    (al ast lp cl : Loc) (x : apply.ApplyKV) (A' : List EntryModel)
    (hnl : mvcc.LogNoLease (kvModel γr.kv A')) (hxl : x.log.length ≤ (kvModel γr.kv A').length) :
    apply.backendOptsOk (snapE E (snapγ γ π0 d'.γB) (metaTM d'.γB P) ci d' g d'.γB al ast lp cl d'.be)
        opts' ∗
      (∀ E1 : apply.AEnv GF, apply.backendOptsOk E1 opts' -∗
        apply.uberIs E1 up' opts' ∗ apply.uberOwn E1 up' (apply.alarmChain E1.authOn false false)) ∗
      srvUberApplyAddr s ↦ (interface.mkOk apply.uberApplier.ty.PointerType #up' : GoInterface) ∗
      srvApi.wSt E.γs (kvModel γr.kv A') (crevOf γr.kv A') ∗ srvApi.crOwn E.γs (crevOf γr.kv A') ∗
      mvcc.api.mvccOpen E.γ ∗
      mvcc.api.mvccBackend E.γ 1 d' (batchLockInv (snapγ γ π0 d'.γB) (metaTM d'.γB P)) ∗
      backend.plHookRO d'.γB g ∗
      lease.leaseOwn (mvcc.api.mvccLeases E.γ) [] ∅ ∗ lease.lessorRdOf (mvcc.api.mvccLeases E.γ) ∗
      lease.leaseRevokers (mvcc.api.mvccLeases E.γ) [] ∗ E.RD ∗
      srvBeAddr s ↦{DFrac.own (1 : Qp).half} srvBeIface d'.be ∗
      dghostVar E.γbe (DFrac.own (1 : Qp).half.half) (bkKey d') ∗
      srvBeRO d' ∗ backend.bkRPool d'.γB d'.P d'.be ∗ apply.bkRT d' ∗
      revAuth E x.log ∗ srvAuthApplyRes s E ∗
      srvWAddr s ↦□ w0 ∗
      waitOk w0 RD0 (fun ot id => waitRegdOpt ρ.wait id ot) (fun ot id => waitGoneOpt ρ.wait id ot) ∗
      RD0 ⊢
    |={⊤}=> ∃ x' : apply.ApplyKV,
      ⌜x'.log = kvModel γr.kv A' ∧ x'.chain = apply.alarmChain E.authOn false false ∧
        x'.crev = crevOf γr.kv A'⌝ ∗
      srvApplyKV s (snapE E (snapγ γ π0 d'.γB) (metaTM d'.γB P) ci d' g d'.γB al ast lp cl d'.be)
        ρ.wait x' := by
  iintro ⟨#Hopts, Hube, Hua, HwSt, HcrO, HmO, HmB, #Hhk, Hlo, Hlr, Hrv, HRD, Hbe, Hγbe, #Hro, Hpl,
    Hrt, Hra, Hauar, #Hw, #Hwok, HRD0⟩
  ihave ⟨#Hub, Huo⟩ :=
    Hube $$ %(snapE E (snapγ γ π0 d'.γB) (metaTM d'.γB P) ci d' g d'.γB al ast lp cl d'.be) Hopts
  ihave #Hlk := leasesKnown_noLease (GF := GF) _ hnl
  have hli : mvcc.leaseItemsOf (mvcc.stateAfter (kvModel γr.kv A')) = ∅ :=
    mvcc.leaseItemsOf_zero _ (mvcc.stateAfter_leaseZero _ hnl)
  imodintro
  iexists ⟨kvModel γr.kv A', apply.alarmChain E.authOn false false, crevOf γr.kv A'⟩
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl⟩
  iunfold srvApplyKV
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
  · iunfold srvAuthApplyRes at Hauar
    unfold srvAuthApplyRes
    simp only [snapE_authMode]
    iexact Hauar
  iexists w0, RD0
  iframe Hw Hwok HRD0

end proof
end EtcdGrove
end Perennial
