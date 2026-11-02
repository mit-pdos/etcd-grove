/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__run.lean`. Lean-first (no Rocq
counterpart); see `InvRun.lean`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__run
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyAll
public import Proof.go_etcd_io.etcd.pkg.v3.schedule.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvServer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SDRun
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.NewFIFOScheduler
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.NewJob
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.Scheduler__Schedule
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__getLead
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__setLead
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__isLeader
public import Spec.go_etcd_io.etcd.pkg.v3.notify.Notifier__Notify
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.ServerStats__BecomeLeader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__getCommittedIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__setCommittedIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__start
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__apply
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetTerm
public import Perennial.Proof.time

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **A job's body** (`s.applyAll(&ep, &ap)`, in the scheduler's goroutine): from the apply
thread's resources at the log `A` (`applyRes`, the previous job's `Post`) and the batch `ce`
raft handed after `A` (`srvC (A ++ ce)`: consecutive indices after `ai₀`, the ids claimed, the
KV's premises from `x₀`), the apply thread's resources at `A ++ ce`. The scheduler's thread token
(in its run token) is the apply thread's while it runs (`srvGoRes`: `GoAttach` of the alarm). The
batch's share of the write budget (`txn.storeWTs`, one token per entry of `ce`) is exactly what
`applyAll` spends: every entry of `ce` is above the applied index (`unapplied ai ce = ce`). -/
theorem run_job_body (hAA : EtcdServer.applyAll.specBatch (GF := GF) (hG := hG))
    (C : ApplyCtx GF) (A ce : List EntryModel)
    (apL : Loc) (es : GoSlice) (ceL : List Loc) (rac nc : GoChan) (γs : schedule.SchedNames)
    (dv : Option Loc) (γnc : NotifyNames)
    (hidx : srvIdxOk C.ai₀ (A ++ ce)) (hok : logShape (A ++ ce))
    (hw : C.γw = C.ρ.wait)
    -- (D43 M3, 2026-10-25) the driver's view, `applyAll`'s (`dvOk`): without one, no conf entry;
    -- with one, a fresh start (`c₀ ≤ ai₀`) at the server's rule (2026-10-30, the repair: one mode)
    (hdvn : dv = none → ∀ m, m ∈ ce → m.typ ≠ W32 1)
    (hdvs : ∀ γn, dv = some γn → uint.Z C.c₀ ≤ uint.Z C.ai₀ ∧
      C.ρ.raft.raft.rule = srvRule C.γr.kv.c0 C.ρ.raft.raft.boot ∧ C.ρ.raft.pre = [] ∧
      C.ρ.raft.ai0 = W64 0)
    -- (2026-10-30, the repair) the node's id, whose applied index `raftAdvancedC`'s close reports
    (nk : GName)
    -- (2026-10-31, #11's S3) a fresh start (`isServerRun`'s)
    (ha00 : uint.nat C.ai₀ = 0)
    -- (2026-10-31, #11) the disk cooperating (`isServerRun`'s), for the snapshot
    (hdisk : storage.diskOk)
    -- (2026-10-31, S1: `applyAll`'s merged snapshot) the batch's raft term, good for its log
    -- (`rnApplyTok_recv`'s `rnRtOk`), at the raft node `γn` of the server's raft; the start's
    -- consistent index at most its applied one (`isServerRun`'s)
    (γn : RNNames) (rt : w64) (hγn : γn.node = C.γr.raft.raft) (hc0 : uint.Z C.c₀ ≤ uint.Z C.ai₀) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerApplyAll C.s C.γr ∗ batchWaitOk C.ρ C.E (A ++ ce) ∗
        taEntriesAddr apL ↦□ es ∗ taRaftAdvancedCAddr apL ↦□ rac ∗
        rnAdvChan rac (letI := srvStor (GF := GF) C.ρ.raft.raft
          iprop(nodeAppliedLb C.ρ.raft.raft.cl nk (uint.nat C.ai₀ + (A ++ ce).length) ∗ nodeCommitLb C.ρ.raft.raft.cl nk (uint.nat C.ai₀ + (A ++ ce).length) ∗
            srvFrozenRange C.γs (uint.nat C.ai₀ + A.length + 1)
              (uint.nat C.ai₀ + (A ++ ce).length + 1) ∗
            srvFrozenTerms C.γs (uint.nat C.ai₀ + 1) (A ++ ce))) ∗
        taSnapshotAddr apL ↦□ (null : Loc) ∗ taNotifycAddr apL ↦□ nc ∗
        isNotify γnc nc (dvView C.ρ.raft dv (A ++ ce)) ∗ notifyRcv γnc ∗
        dvView C.ρ.raft dv A ∗ dvRes C.s C.ρ.raft dv (A ++ ce) ∗ (match dv with | none => iprop(True) | some n => (letI := srvStor (GF := GF) C.ρ.raft.raft; nodeRunning n C.ρ.raft.raft.cl srvClusterN (1 : Qp).half)) ∗
        es ↦*□ ceL ∗ entriesAt ceL ce ∗ batchCommittedIdx C.γr ce ∗ schedule.schedRunning γs ∗
        applyRes C A ∗ srvWTPool C.E C.wt ∗ srvRLogLb C.ρ.raft (A ++ ce) ∗
        srvSnapDisk C.s C.γr ∗
        (letI : MemStorReg GF := ⟨C.γr.raft.raft.reg⟩; memStorInv C.ms C.γs C.γr.raft.raft.cl nk) ∗
        taRaftTermAddr apL ↦□ rt ∗ rnRtOk γn rt (rnLogOf γn (A ++ ce)).length }}
      (App (App (Val (C.s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyAll")) (Val #C.ep))
        (Val #apL))
    {{ RET #(); schedule.schedRunning γs ∗ applyRes C (A ++ ce) ∗ (match dv with | none => iprop(True) | some n => (letI := srvStor (GF := GF) C.ρ.raft.raft; nodeRunning n C.ρ.raft.raft.cl srvClusterN (1 : Qp).half)) }} := by
  have hR : ∀ dv : Option Loc, (match dv with | none => iprop(True) | some n => (letI := srvStor (GF := GF) C.ρ.raft.raft; nodeRunning n C.ρ.raft.raft.cl srvClusterN (1 : Qp).half)) =
      srvRunH (GF := GF) C.ρ.raft dv := fun dv => by cases dv <;> rfl
  simp only [EtcdServer.applyAll.specBatch, srvRunH_applyAll_spec] at hAA
  rw [hR]
  iintro %Φ ⟨#Hpkg, #Hsa, #Hbw, #Hes, #Hrac, #Hracc, #Hsn, #Hnc, #Hncb, Hnrc, Hdv, #Hdvr, Hrh, #Hesl,
    #Hents, #Hbc, Hrun, HR, #HWc, #Hlbr, #Hsd, #Hmsinv, #Hrtf, #Hrtok⟩ HΦ
  iunfold applyRes at HR
  icases HR with ⟨%B, %st, %ai, %at', %a, %t, %cs, %x, %HB, #Hsrv, Hai, Hat, Hcs, #Hcv, Hss, Hst, Hbe, Happ, Hlr, Hbr,
    Hwr, HKV, Hao, #Hlog, Hkr, HRS, HAR, #HKVf, Hwal, ⟨%w, #HWA⟩, Hso, %Hpure⟩
  rw [hw]
  obtain ⟨Hloop, Hai0, HJ, Hci, Hlt⟩ := Hpure
  -- (S1) the consistent index at most the applied one (a fresh start's at most its applied index)
  have hcia : uint.Z (ciEff B.γ st.k) ≤ uint.Z ai := by
    rcases HJ with h1 | ⟨-, h2⟩
    · rw [h1]; have : (0 : Int) ≤ A.length := by omega
      omega
    · exact h2
  iunfold schedule.schedRunning at Hrun
  icases Hrun with ⟨Hrt, Htok⟩
  have habove := srvIdxOk_batch_above C.ai₀ ai A ce hidx Hai0
  have hun : unapplied ai ce = ce := unapplied_all ai ce habove
  have hcong : ∀ m ∈ ce, (uint.Z (ciEff B.γ st.k) < uint.Z m.index ↔ uint.Z C.c₀ < uint.Z m.index) :=
    fun m hm => ciJ_iff _ _ _ HJ m (habove m hm)
  have hok' : logShape (unapplied ai ce) := by
    rw [hun]
    exact ((logShape_append A ce).1 hok).2
  have hb1 : uint.Z ai + 1 < 2 ^ 64 := by
    have h1 := hidx.1
    simp only [List.length_append] at h1
    push_cast at h1
    have : (0 : Int) ≤ ce.length := by omega
    omega
  -- (D43 M3) the view's premise: a fresh start's consistent index is at most the applied one
  have hdv : dvOk C.ρ.raft C.γr.kv.c0 dv (ciEff B.γ st.k) (ai + 1) (unapplied ai ce) := by
    rw [hun]
    refine ⟨hdvn, fun γn h => ⟨?_, (hdvs γn h).2⟩⟩
    have hc0 := (hdvs γn h).1
    have hai1 : uint.Z (ai + 1) = uint.Z ai + 1 := by word
    rw [hai1]
    rcases HJ with h1 | ⟨-, h2⟩
    · rw [h1]
      have : (0 : Int) ≤ A.length := by omega
      omega
    · omega
  have hms : ce = [] ∨ (entriesFrom (ai + 1) ce ∧ uint.Z (ai + 1) ≤ uint.Z ai + 1) := by
    by_cases hne : ce = []
    · left; exact hne
    · right
      obtain ⟨h1, h2⟩ := srvIdxOk_batch_from C.ai₀ ai A ce hidx Hai0 hne
      exact ⟨h1, by omega⟩
  ihave #Hbw' : iprop(batchWaitOk C.ρ B.E ce) $$ []
  · rw [batchWaitOk_beSucc HB]
    iunfold batchWaitOk at Hbw
    iunfold batchWaitOk
    imodintro
    iintro %m %hm
    iapply Hbw
    ipureintro; exact List.mem_append_right A hm
  ihave #Hsrv2 := Hsrv
  iunfold isServer at Hsrv2
  icases Hsrv2 with ⟨%Hρr, -⟩
  iunfold kvRun at Hkr
  icases Hkr with ⟨Hka, %Hkc⟩
  ihave #Hkb : iprop(kvBatch C.γr (ciEff B.γ st.k) ai A ce) $$ []
  · iunfold kvBatch
    isplitr
    · rw [← Hρr]; iexact Hlbr
    ipureintro
    refine ⟨by rw [Hkc.2]; exact Hai0, fun m hm => ?_⟩
    rw [Hkc.1]; exact hcong m hm
  -- (D19i part 1) the floor past the batch, at its last index (`srvIdxOk_batch_last`)
  have e1 : (max (uint.Z ai) (((ce.getLast?).map (fun m => uint.Z m.index)).getD 0)).toNat =
      uint.nat C.ai₀ + (A ++ ce).length := by
    rw [srvIdxOk_batch_last C.ai₀ ai A ce hidx Hai0]; word
  have e2 : uint.nat ai + 1 = uint.nat C.ai₀ + A.length + 1 := by word
  ihave #Hracc' : rnAdvChan rac (letI := srvStor (GF := GF) C.ρ.raft.raft
      iprop(nodeAppliedLb C.ρ.raft.raft.cl nk
        (max (uint.Z ai) (((ce.getLast?).map (fun m => uint.Z m.index)).getD 0)).toNat ∗ nodeCommitLb C.ρ.raft.raft.cl nk
        (max (uint.Z ai) (((ce.getLast?).map (fun m => uint.Z m.index)).getD 0)).toNat ∗
        srvFrozenRange C.γs (uint.nat ai + 1)
          ((max (uint.Z ai) (((ce.getLast?).map (fun m => uint.Z m.index)).getD 0)).toNat + 1) ∗
        srvFrozenTerms C.γs 1 (A ++ ce))) $$ []
  · rw [e1, e2]; iExactEq Hracc; rw [ha00]
  ihave #HWc' : iprop(srvWTPool B.E C.wt) $$ []
  · rw [srvWTPool_beSucc HB]; iexact HWc
  ihave Hbr : iprop(srvBemuReaderAt C.s B.E.γbe) $$ [Hbr]
  · rw [beSucc_γbe HB]; iexact Hbr
  iapply (hAA C.s B.γ C.ci B.TM B.E C.ρ C.γr B.b C.ep apL es ceL ce (ai + 1) rac nc st ai at' a t cs x A
      C.ms C.γs C.wt dv γnc w nk (1 : Qp).half γn rt (rnLogOf γn (A ++ ce)).length hms hb1 Hloop hok' hdv (by have := uint_nat_eq C.ai₀; omega) Hlt
      hdisk Hci hcia hγn (by rw [hun]; simp [rnLogOf]))
    $$ [Hai Hat Hcs Hcv Hss Hst Hbe Happ Hlr Hwr Htok Hbr HKV Hao Hka HRS Hnrc Hdv HAR Hrh Hwal Hso]
  · rw [hun]
    iframe Hsd Hmsinv HKVf Hwal Hrtf Hrtok
    iframe HWc' Hracc' Hcv Hkb Hbw' HWA Hlog Hsrv Hbc Hents Hesl Hncb Hnc Hsn Hrac Hes Hsa Hpkg
    iframe
    iunfold srvGoRes
    iframe
    iexact Hdvr
  inext
  iintro ⟨%γ', %TM', %E', %b', %st', %ai', %at'', %a', %t', %cs', %HB', Hrh, #Hsrv', HAR, Hai, Hat, Hcs, #Hcv', Hss, Hst, Hbe, Happ, Hlr, Hgr, Hbr, Hao,
      #Hlb, #HWA', ⟨%x', HKV, %Hx', #Hlog', Hka, HRS⟩, #HKVf', Hwal, Hso, %Hpost⟩
  obtain ⟨hloop', hai', hci', hciN, hat'⟩ := Hpost
  iunfold srvGoRes at Hgr
  icases Hgr with ⟨Hwr, Htok⟩
  iapply HΦ
  iunfold schedule.schedRunning
  iframe Hrt Htok Hrh
  ihave Hkr : iprop(kvRun C.γr C.ai₀ C.c₀ (A ++ ce) x') $$ [Hka]
  · iunfold kvRun
    isplitl [Hka]
    · iapply (show kvApplied (GF := GF) C.γr.raft C.γr.kv (A ++ unapplied ai ce) x' ⊢
        kvApplied C.γr.raft C.γr.kv (A ++ ce) x' from by rw [hun]) $$ Hka
    ipureintro; exact Hkc
  ihave HRS : iprop(srvRest E' C.γr (A ++ ce)) $$ [HRS]
  · iapply (show srvRest (GF := GF) E' C.γr (A ++ unapplied ai ce) ⊢ srvRest E' C.γr (A ++ ce)
      from by rw [hun]) $$ HRS
  ihave HAR : iprop(srvApRes C.s C.γr (A ++ ce)) $$ [HAR]
  · iapply (show srvApRes (GF := GF) C.s C.γr (A ++ unapplied ai ce) ⊢ srvApRes C.s C.γr (A ++ ce)
      from by rw [hun]) $$ HAR
  ihave Hbr : iprop(srvBemuReaderAt C.s C.E.γbe) $$ [Hbr]
  · rw [← beSucc_γbe HB]; iexact Hbr
  iunfold applyRes
  rw [hw]
  iexists ⟨γ', TM', E', b'⟩, st', ai', at'', a', t', cs', x'
  isplitr
  · ipureintro; exact beSucc_trans HB HB'
  iframe Hsrv'
  ihave #Hcv'' : epCsAt C.ρ.raft (A ++ ce) cs' $$ []
  · rw [show A ++ ce = A ++ unapplied ai ce by rw [hun]]; iexact Hcv'
  iframe Hcv'' HKVf'
  iframe
  iframe Hlog'
  have hlast := srvIdxOk_batch_last C.ai₀ ai A ce hidx Hai0
  isplitr
  · iexists w + (unapplied ai ce).length
    iexact HWA'
  ipureintro
  rw [hun] at Hx'
  refine ⟨hloop', by rw [hai', hlast], ?_, hciN Hci, ?_⟩
  · apply ciJ_step _ _ _ ai ai' HJ (by rw [hai']; omega) hci'
  · rw [hun] at hat'; exact lastTermIs_append Hlt hat'

/-- `run_job_body`'s running half, as `srvRunH` (`SDRun.lean`). -/
theorem run_job_body_match (γs : ServerRaftNames) (dv : Option Loc) :
    run_job_body.match_1 (fun _ => IProp GF) dv (fun _ => iprop(True))
      (fun n => letI := srvStor (GF := GF) γs.raft; nodeRunning (GF := GF) n γs.raft.cl srvClusterN (1 : Qp).half) =
      srvRunH (GF := GF) γs dv := by
  cases dv <;> rfl

/-- (open, J8b, 2026-11-01) **`run_job_snap` in the compaction mode** (`E.cmp = true`): not
proved. `applyAll.specSnap` takes the compaction off (the closer it hands `applySnapshot` is
`srvKVCloserW`, `srvKVCloser` only with the mode off); a snapshot in the compaction mode needs
`specSnap` generalized to it, a stage of its own (`notes/snapshot-j8a-plan.md`, J8b). -/
theorem run_job_snap_cmp (hAA : EtcdServer.applyAll.specSnap (GF := GF) (hG := hG))
    (C : ApplyCtx GF) (A A' : List EntryModel) (apL : Loc) (es : GoSlice) (sn : Loc)
    (sv : SnapshotM) (rac nc : GoChan) (γs : schedule.SchedNames) (γnc : NotifyNames)
    (γn : RNNames) (rt : w64)
    (ha00 : uint.nat C.ai₀ = 0) (hc0 : uint.Z C.c₀ ≤ uint.Z C.ai₀) (hpre : γn.pre = [])
    (hγn : γn.node = C.γr.raft.raft) (hρ : C.ρ.raft = C.γr.raft)
    (hpr : C.γr.raft.pre = γn.pre) (hγs : C.γs = γn.γs) (hγw : C.γw = C.ρ.wait)
    (hlt : A.length < A'.length)
    (hlen : (γn.pre ++ A').length = uint.nat sv.Metadata'.Index')
    (h61 : uint.Z sv.Metadata'.Index' < 2 ^ 61)
    (hboot : (γn.node.boot.length : Int) ≤ uint.Z sv.Metadata'.Index')
    (hcmp : C.E.cmp = true) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerApplyAll C.s C.γr ∗ srvMemberIDAddr C.s ↦□ γn.id ∗ srvMetaSnap C.γ ∗
        taEntriesAddr apL ↦□ es ∗ es ↦*□ ([] : List Loc) ∗
        taSnapshotAddr apL ↦□ sn ∗ ownSnapM sn DFrac.discard sv ∗
        (letI := srvStor (GF := GF) γn.node; iprop(
          snapshotCert γn.node.cl srvClusterN (snapTrip sv sv.Metadata'.ConfState'.lists) ∗
          nodeSnapLocal γn.node.cl γn.id sv.Metadata'.Index')) ∗
        taNotifycAddr apL ↦□ nc ∗ isNotify2 γnc nc iprop(True) iprop(True) ∗ notifyRcvN γnc 0 ∗
        taRaftAdvancedCAddr apL ↦□ rac ∗
        rnAdvChan rac (letI := srvStor (GF := GF) γn.node
          iprop(nodeAppliedLb γn.node.cl γn.key (γn.pre ++ A').length ∗
            nodeCommitLb γn.node.cl γn.key (γn.pre ++ A').length ∗
            srvFrozenAt γn.γs (γn.pre ++ A').length ∗ srvFrozenBelow γn.γs (γn.pre ++ A').length)) ∗
        taRaftTermAddr apL ↦□ rt ∗ rnRtOk γn rt (rnLogOf γn A').length ∗
        schedule.schedRunning γs ∗ applyRes C A ∗ srvWTPool C.E C.wt ∗ srvRLogLb C.ρ.raft A' }}
      (App (App (Val (C.s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyAll")) (Val #C.ep))
        (Val #apL))
    {{ RET #(); schedule.schedRunning γs ∗ applyRes C A' }} := by
  sorry

/-- (open, the lease-grant plan's D2, 2026-11-02) **`run`'s snapshot job in a cluster that grants
leases** (`runSnapLgOk`, `InvRun.lean`): not proved. `run` does not use it: it takes the case as
`isServerRun`'s premise `γr.kv.lg = true → lease.leasesNoExpiry ∧ runSnapLgOk` (from `NewServer`'s precondition), which a
cluster that grants none discharges by its `lg = false`; only a lease-granting result
(`leasegrant.wp_Main`) uses this theorem, so it is in their trust base only. -/
theorem runSnapLgOk_open : runSnapLgOk (GF := GF) := by
  sorry

/-- **A snapshot payload's job** (J8b, 2026-11-01; `s.applyAll(&ep, &ap)` on raft's snapshot
payload, `rnApplyTok_recv`'s second case): from the apply thread's resources at the log `A`
(`applyRes`) and the payload that jumps raft's log to `A'` (`|A| < |A'|`, of length the snapshot's
index), the apply thread's resources at `A'`, over `applyAll.specSnap`: the image's log is raft's
`A'` (both committed, of the same length), the applied index and the consistent index the
snapshot's (`ciJ`'s second disjunct, a fresh start's `c₀ = 0`). The member's id and the meta
reads are `isServerRun`'s (`#Hmid`, `#HmetaSnap`), the index past the boot log the payload's
(`rnReadySnap_bootLen`, open). In the compaction mode, `run_job_snap_cmp` (open); in a cluster that grants leases, the
premise `hslg` (its `runSnapLgOk`, `isServerRun`'s `%Hslg`, opened by `runSnapLgOk_elim`). -/
theorem run_job_snap (hAA : EtcdServer.applyAll.specSnap (GF := GF) (hG := hG))
    (C : ApplyCtx GF) (A A' : List EntryModel) (apL : Loc) (es : GoSlice) (sn : Loc)
    (sv : SnapshotM) (rac nc : GoChan) (γs : schedule.SchedNames) (γnc : NotifyNames)
    (γn : RNNames) (rt : w64)
    (ha00 : uint.nat C.ai₀ = 0) (hc0 : uint.Z C.c₀ ≤ uint.Z C.ai₀) (hpre : γn.pre = [])
    (hγn : γn.node = C.γr.raft.raft) (hρ : C.ρ.raft = C.γr.raft)
    (hpr : C.γr.raft.pre = γn.pre) (hγs : C.γs = γn.γs) (hγw : C.γw = C.ρ.wait)
    (hlt : A.length < A'.length)
    (hlen : (γn.pre ++ A').length = uint.nat sv.Metadata'.Index')
    (h61 : uint.Z sv.Metadata'.Index' < 2 ^ 61)
    (hboot : (γn.node.boot.length : Int) ≤ uint.Z sv.Metadata'.Index')
    (hslg : C.γr.kv.lg = true → lease.leasesNoExpiry ∧ runSnapLgOk (GF := GF)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerApplyAll C.s C.γr ∗ srvMemberIDAddr C.s ↦□ γn.id ∗ srvMetaSnap C.γ ∗
        taEntriesAddr apL ↦□ es ∗ es ↦*□ ([] : List Loc) ∗
        taSnapshotAddr apL ↦□ sn ∗ ownSnapM sn DFrac.discard sv ∗
        (letI := srvStor (GF := GF) γn.node; iprop(
          snapshotCert γn.node.cl srvClusterN (snapTrip sv sv.Metadata'.ConfState'.lists) ∗
          nodeSnapLocal γn.node.cl γn.id sv.Metadata'.Index')) ∗
        taNotifycAddr apL ↦□ nc ∗ isNotify2 γnc nc iprop(True) iprop(True) ∗ notifyRcvN γnc 0 ∗
        taRaftAdvancedCAddr apL ↦□ rac ∗
        rnAdvChan rac (letI := srvStor (GF := GF) γn.node
          iprop(nodeAppliedLb γn.node.cl γn.key (γn.pre ++ A').length ∗
            nodeCommitLb γn.node.cl γn.key (γn.pre ++ A').length ∗
            srvFrozenAt γn.γs (γn.pre ++ A').length ∗ srvFrozenBelow γn.γs (γn.pre ++ A').length)) ∗
        taRaftTermAddr apL ↦□ rt ∗ rnRtOk γn rt (rnLogOf γn A').length ∗
        schedule.schedRunning γs ∗ applyRes C A ∗ srvWTPool C.E C.wt ∗ srvRLogLb C.ρ.raft A' }}
      (App (App (Val (C.s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyAll")) (Val #C.ep))
        (Val #apL))
    {{ RET #(); schedule.schedRunning γs ∗ applyRes C A' }} := by
  cases hlgc : C.γr.kv.lg
  case true =>
    exact runSnapLgOk_elim (hslg hlgc).2 C A A' apL es sn sv rac nc γs γnc γn rt ha00 hc0 hpre hγn hρ hpr hγs hγw hlt
      hlen h61 hboot hlgc
  cases hcm : C.E.cmp
  · iintro %Φ ⟨#Hpkg, #Hsa, #Hmid, #Hmeta, #Hes, #Hesl, #Hsnf, Hsnv, #Hcl, #Hncf, #Hnc2, Hnr0,
      #Hracf, #Hracc, #Hrtf, #Hrtok, Hrun, HR, #HWc, #Hlbr⟩ HΦ
    iunfold applyRes at HR
    icases HR with ⟨%B, %st, %ai, %at', %a, %t, %cs, %x, %HB, #Hsrv, Hai, Hat, Hcs, #Hcv, Hss,
      Hst, Hbe, Happ, Hlr, Hbr, Hwr, HKV, Hao, #Hlog, Hkr, HRS, HAR, #HKVf, Hwal, ⟨%w, #HWA⟩, Hso,
      %Hpure⟩
    obtain ⟨Hloop, Hai0, HJ, Hci, Hlt⟩ := Hpure
    iunfold kvRun at Hkr
    icases Hkr with ⟨Hka, %Hkc⟩
    iunfold schedule.schedRunning at Hrun
    icases Hrun with ⟨Hrt0, Htok⟩
    -- the fresh start's facts
    have hai0 : C.ai₀ = W64 0 := by have := uint_nat_eq C.ai₀; word
    have hpre' : C.γr.raft.pre = [] := by rw [hpr]; exact hpre
    have hiA : (uint.nat sv.Metadata'.Index' : Int) = A'.length := by rw [← hlen, hpre]; simp
    have hiZ := uint_nat_eq sv.Metadata'.Index'
    have hz0 : uint.Z (W64 0) = 0 := by word
    have hAL : uint.Z ai = A.length := by rw [Hai0, hai0, hz0]; simp
    have hai : uint.Z ai < uint.Z sv.Metadata'.Index' := by
      have : (A.length : Int) < A'.length := by exact_mod_cast hlt
      omega
    have hcia : uint.Z (ciEff B.γ st.k) ≤ uint.Z ai := by
      rcases HJ with h1 | ⟨-, h2⟩
      · rw [h1]; have : (0 : Int) ≤ A.length := by omega
        rw [hai0] at hc0; omega
      · exact h2
    have hc00 : C.c₀ = W64 0 := by rw [hai0] at hc0; word
    have hraft : C.γr.raft = ⟨C.γr.raft.raft, [], W64 0⟩ := by
      have h1 := Hkc.2
      rw [hai0] at h1
      cases hr : C.γr.raft
      simp only [hr] at hpre' h1
      simp [hpre', h1]
    ihave #Hsrv' := Hsrv
    iunfold isServer at Hsrv'
    icases Hsrv' with ⟨-, -, -, #Hatm, -, -⟩
    iunfold srvAtomics at Hatm
    icases Hatm with ⟨-, -, #Hkvi⟩
    iunfold srvKVInvs at Hkvi
    icases Hkvi with ⟨#Hkv, -⟩
    imod kvInv_ch0_off C.γr.raft C.γr.kv $$ Hkv with %hch
    ihave #Hsa' := Hsa
    iunfold isServerApplyAll at Hsa'
    icases Hsa' with ⟨%wt0, %msc, %sc, -, -, -, -, -, -, -, -, -, -, -, %Hlog0⟩
    have hcmB : B.E.cmp = false := by
      obtain ⟨-, p, P, f, c, RO, RW, hE⟩ := HB
      rw [hE]; exact hcm
    have hn : uint.nat sv.Metadata'.Index' ≤ (rnLogOf γn A').length := by
      simp only [rnLogOf, List.length_map]; omega
    -- the job's resources at the current backend `B`
    ihave #HWc' : iprop(srvWTPool B.E C.wt) $$ []
    · rw [srvWTPool_beSucc HB]; iexact HWc
    ihave Hbr : iprop(srvBemuReaderAt C.s B.E.γbe) $$ [Hbr]
    · rw [beSucc_γbe HB]; iexact Hbr
    ihave #Hmeta' : srvMetaSnap B.γ $$ []
    · have hms : srvMetaSnap (GF := GF) B.γ = srvMetaSnap C.γ := by
        rw [HB.1]; exact srvMetaSnap_withPh _ _
      rw [hms]; iexact Hmeta
    iunfold srvMetaSnap at Hmeta'
    ihave #Hracc' : rnAdvChan rac (letI := srvStor (GF := GF) C.ρ.raft.raft
        iprop(nodeAppliedLb C.ρ.raft.raft.cl γn.key (uint.nat sv.Metadata'.Index') ∗
          nodeCommitLb C.ρ.raft.raft.cl γn.key (uint.nat sv.Metadata'.Index') ∗
          srvFrozenAt C.γs (uint.nat sv.Metadata'.Index') ∗
          srvFrozenBelow C.γs (uint.nat sv.Metadata'.Index'))) $$ []
    · rw [hρ, ← hγn, hγs, ← hlen]; iexact Hracc
    ihave #Hcl' : (letI := srvStor (GF := GF) C.γr.raft.raft; iprop(
        snapshotCert C.γr.raft.raft.cl srvClusterN (snapTrip sv sv.Metadata'.ConfState'.lists) ∗
        nodeSnapLocal C.γr.raft.raft.cl γn.id sv.Metadata'.Index')) $$ []
    · rw [← hγn]; iexact Hcl
    ihave HKV : srvApplyKV C.s B.E C.ρ.wait x $$ [HKV]
    · rw [← hγw]; iexact HKV
    iapply (hAA C.s B.γ C.ci B.TM B.E C.ρ C.γr B.b C.ep apL es sn sv rac nc st ai at' a t cs x A
      C.ms C.γs C.wt γnc w γn.id γn.key (1 : Qp).half γn rt (rnLogOf γn A').length hai h61
      (by rw [← hγn]; exact hboot) hAL hcia hraft (by rw [Hkc.1, hc00]) hch Hlog0 hcmB hlgc hγn hn)
      $$ [Hai Hat Hcs Hss Hst Hbe Happ Hlr Hwr Htok Hbr HKV Hao Hka HRS HAR Hwal Hso Hsnv Hnr0]
    · iframe #
      iframe
      iunfold srvGoRes
      iframe
    inext
    iintro ⟨%γ', %TM', %E', %b', %st', %A'', %cs', %HB', #Hsrv'', HAR, #Hlb'', Hai, Hat, Hcs,
      #Hcv', Hss, Hst, Hbe, Happ, Hlr, Hgr, Hbr, Hao, #Hal, #HWA', ⟨%x', HKV, #Hlog', Hka, HRS⟩,
      #HKVf', Hwal, Hso, %Hpost⟩
    obtain ⟨hloop', hci', -, hlen'', hlast⟩ := Hpost
    -- the image's log is raft's `A'`: both committed, of the snapshot's length
    ihave #Hlbr' : srvRLogLb C.γr.raft A' $$ []
    · rw [← hρ]; iexact Hlbr
    ihave %Hpf := srvRLogLb_prefix C.γr.raft A'' A' $$ [Hlb'' Hlbr']
    · iframe Hlb'' Hlbr'
    have hA : A'' = A' := by
      have h1 : A''.length = A'.length := by
        rw [hpre'] at hlen''; simp only [List.nil_append] at hlen''; omega
      rcases Hpf with h | h
      · exact h.eq_of_length h1
      · exact (h.eq_of_length h1.symm).symm
    subst hA
    iunfold srvGoRes at Hgr
    icases Hgr with ⟨Hwr, Htok⟩
    ihave HKV : srvApplyKV C.s E' C.γw x' $$ [HKV]
    · rw [hγw]; iexact HKV
    iapply HΦ
    iunfold schedule.schedRunning
    iframe Hrt0 Htok
    ihave Hbr : iprop(srvBemuReaderAt C.s C.E.γbe) $$ [Hbr]
    · rw [← beSucc_γbe HB]; iexact Hbr
    iunfold applyRes
    iexists ⟨γ', TM', E', b'⟩, st', sv.Metadata'.Index', sv.Metadata'.Term', a, t, cs', x'
    isplitr
    · ipureintro; exact beSucc_trans HB HB'
    iframe Hsrv'' Hcv' HKVf' Hlog'
    iframe
    isplitl [Hka]
    · iunfold kvRun
      iframe Hka
      ipureintro; exact Hkc
    isplitr
    · iexists w; iexact HWA'
    ipureintro
    refine ⟨hloop', ?_, ?_, by rw [hci']; exact Int.le_refl _, hlast⟩
    · rw [hai0, hz0]; omega
    · right; rw [hci', hc00]; simp
  · exact run_job_snap_cmp hAA C A A' apL es sn sv rac nc γs γnc γn rt ha00 hc0 hpre hγn hρ hpr hγs
      hγw hlt hlen h61 hboot hcm

/-- **The apply side's half of the running token, lent to a job** (2026-10-30, the repair): the
job's view `rnDv γn ce` is the node's or none; with the node's, the half is `srvRunH`'s. -/
theorem srvRunH_lend (γn : RNNames) (γs : ServerRaftNames) (hnd : γs.raft = γn.node)
    (ce : List EntryModel) :
    (letI := srvStor (GF := GF) γn.node; nodeRunning (GF := GF) γn.nl γn.node.cl srvClusterN (1 : Qp).half) ⊢
      srvRunH (GF := GF) γs (rnDv γn ce) ∗
        (srvRunH (GF := GF) γs (rnDv γn ce) -∗
          (letI := srvStor (GF := GF) γn.node; nodeRunning (GF := GF) γn.nl γn.node.cl srvClusterN (1 : Qp).half)) := by
  unfold rnDv
  split
  · rw [srvRunH_some, hnd]
    iintro H
    iframe H
    iintro H; iexact H
  · rw [srvRunH_none]
    iintro H
    isplitr
    · itrivial
    iintro -; iexact H

/-- **A job's body in the mode `on`** (the auth plan's E3q; `run_job_body`'s over
`applyAll.specOn`). Formerly: **A job's body** (`s.applyAll(&ep, &ap)`, in the scheduler's goroutine): from the apply
thread's resources at the log `A` (`applyRes`, the previous job's `Post`) and the batch `ce`
raft handed after `A` (`srvC (A ++ ce)`: consecutive indices after `ai₀`, the ids claimed, the
KV's premises from `x₀`), the apply thread's resources at `A ++ ce`. The scheduler's thread token
(in its run token) is the apply thread's while it runs (`srvGoRes`: `GoAttach` of the alarm). The
batch's share of the write budget (`txn.storeWTs`, one token per entry of `ce`) is exactly what
`applyAll` spends: every entry of `ce` is above the applied index (`unapplied ai ce = ce`). -/
theorem run_job_bodyOn (hAA : EtcdServer.applyAll.specOn (GF := GF) (hG := hG))
    (C : ApplyCtx GF) (A ce : List EntryModel)
    (γa : auth.AuthNames) (hM : C.E.authMode = .on γa) (hRB : receiptBound GF ≤ 2 ^ 48)
    (apL : Loc) (es : GoSlice) (ceL : List Loc) (rac nc : GoChan) (γs : schedule.SchedNames)
    (dv : Option Loc) (γnc : NotifyNames)
    (hidx : srvIdxOk C.ai₀ (A ++ ce)) (hok : logShapeOn (A ++ ce))
    (hw : C.γw = C.ρ.wait)
    -- (D43 M3, 2026-10-25) the driver's view, `applyAll`'s (`dvOk`): without one, no conf entry;
    -- with one, a fresh start (`c₀ ≤ ai₀`) at the server's rule (2026-10-30, the repair: one mode)
    (hdvn : dv = none → ∀ m, m ∈ ce → m.typ ≠ W32 1)
    (hdvs : ∀ γn, dv = some γn → uint.Z C.c₀ ≤ uint.Z C.ai₀ ∧
      C.ρ.raft.raft.rule = srvRule C.γr.kv.c0 C.ρ.raft.raft.boot ∧ C.ρ.raft.pre = [] ∧
      C.ρ.raft.ai0 = W64 0)
    -- (2026-10-30, the repair) the node's id, whose applied index `raftAdvancedC`'s close reports
    (nk : GName)
    -- (2026-10-31, #11's S3) a fresh start (`isServerRun`'s)
    (ha00 : uint.nat C.ai₀ = 0)
    -- (2026-10-31, #11) the disk cooperating (`isServerRun`'s), for the snapshot
    (hdisk : storage.diskOk)
    -- (2026-10-31, S1: `applyAll`'s merged snapshot) the batch's raft term, good for its log
    -- (`rnApplyTok_recv`'s `rnRtOk`), at the raft node `γn` of the server's raft; the start's
    -- consistent index at most its applied one (`isServerRun`'s)
    (γn : RNNames) (rt : w64) (hγn : γn.node = C.γr.raft.raft) (hc0 : uint.Z C.c₀ ≤ uint.Z C.ai₀) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        srvLessorNil C.s ∗ isServerApplyAll C.s C.γr ∗ batchWaitOk C.ρ C.E (A ++ ce) ∗
        taEntriesAddr apL ↦□ es ∗ taRaftAdvancedCAddr apL ↦□ rac ∗
        rnAdvChan rac (letI := srvStor (GF := GF) C.ρ.raft.raft
          iprop(nodeAppliedLb C.ρ.raft.raft.cl nk (uint.nat C.ai₀ + (A ++ ce).length) ∗ nodeCommitLb C.ρ.raft.raft.cl nk (uint.nat C.ai₀ + (A ++ ce).length) ∗
            srvFrozenRange C.γs (uint.nat C.ai₀ + A.length + 1)
              (uint.nat C.ai₀ + (A ++ ce).length + 1) ∗
            srvFrozenTerms C.γs (uint.nat C.ai₀ + 1) (A ++ ce))) ∗
        taSnapshotAddr apL ↦□ (null : Loc) ∗ taNotifycAddr apL ↦□ nc ∗
        isNotify γnc nc (dvView C.ρ.raft dv (A ++ ce)) ∗ notifyRcv γnc ∗
        dvView C.ρ.raft dv A ∗ dvRes C.s C.ρ.raft dv (A ++ ce) ∗ (match dv with | none => iprop(True) | some n => (letI := srvStor (GF := GF) C.ρ.raft.raft; nodeRunning n C.ρ.raft.raft.cl srvClusterN (1 : Qp).half)) ∗
        es ↦*□ ceL ∗ entriesAt ceL ce ∗ batchCommittedIdx C.γr ce ∗ schedule.schedRunning γs ∗
        applyResOn C A ∗ srvWTPool C.E C.wt ∗ srvRLogLb C.ρ.raft (A ++ ce) ∗
        srvSnapDisk C.s C.γr ∗
        (letI : MemStorReg GF := ⟨C.γr.raft.raft.reg⟩; memStorInv C.ms C.γs C.γr.raft.raft.cl nk) ∗
        taRaftTermAddr apL ↦□ rt ∗ rnRtOk γn rt (rnLogOf γn (A ++ ce)).length }}
      (App (App (Val (C.s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyAll")) (Val #C.ep))
        (Val #apL))
    {{ RET #(); schedule.schedRunning γs ∗ applyResOn C (A ++ ce) ∗ (match dv with | none => iprop(True) | some n => (letI := srvStor (GF := GF) C.ρ.raft.raft; nodeRunning n C.ρ.raft.raft.cl srvClusterN (1 : Qp).half)) }} := by
  have hR : ∀ dv : Option Loc, (match dv with | none => iprop(True) | some n => (letI := srvStor (GF := GF) C.ρ.raft.raft; nodeRunning n C.ρ.raft.raft.cl srvClusterN (1 : Qp).half)) =
      srvRunH (GF := GF) C.ρ.raft dv := fun dv => by cases dv <;> rfl
  simp only [EtcdServer.applyAll.specOn, srvRunH_applyAll_spec] at hAA
  rw [hR]
  iintro %Φ ⟨#Hpkg, #Hlnil, #Hsa, #Hbw, #Hes, #Hrac, #Hracc, #Hsn, #Hnc, #Hncb, Hnrc, Hdv, #Hdvr, Hrh, #Hesl,
    #Hents, #Hbc, Hrun, HR, #HWc, #Hlbr, #Hsd, #Hmsinv, #Hrtf, #Hrtok⟩ HΦ
  iunfold applyResOn at HR
  icases HR with ⟨%B, %st, %ai, %at', %a, %t, %cs, %x, %sa, %HB, #Hsrv, Hai, Hat, Hcs, #Hcv, Hss, Hst, Hbe, Happ, Hlr, Hbr,
    Hwr, HKV, Hao, #Hlog, Hkr, HRS, HAR, #HKVf, Hwal, ⟨%w, #HWA⟩, HtokR, Hso, %Hpure⟩
  rw [hw]
  obtain ⟨Hloop, Hai0, HJ, Hci, Hlt⟩ := Hpure
  -- (S1) the consistent index at most the applied one (a fresh start's at most its applied index)
  have hcia : uint.Z (ciEff B.γ st.k) ≤ uint.Z ai := by
    rcases HJ with h1 | ⟨-, h2⟩
    · rw [h1]; have : (0 : Int) ≤ A.length := by omega
      omega
    · exact h2
  iunfold schedule.schedRunning at Hrun
  icases Hrun with ⟨Hrt, Htok⟩
  have habove := srvIdxOk_batch_above C.ai₀ ai A ce hidx Hai0
  have hun : unapplied ai ce = ce := unapplied_all ai ce habove
  have hcong : ∀ m ∈ ce, (uint.Z (ciEff B.γ st.k) < uint.Z m.index ↔ uint.Z C.c₀ < uint.Z m.index) :=
    fun m hm => ciJ_iff _ _ _ HJ m (habove m hm)
  have hok' : logShapeOn (unapplied ai ce) := by
    rw [hun]
    exact fun m hm => hok m (List.mem_append_right A hm)
  have hb1 : uint.Z ai + 1 < 2 ^ 64 := by
    have h1 := hidx.1
    simp only [List.length_append] at h1
    push_cast at h1
    have : (0 : Int) ≤ ce.length := by omega
    omega
  -- (D43 M3) the view's premise: a fresh start's consistent index is at most the applied one
  have hdv : dvOk C.ρ.raft C.γr.kv.c0 dv (ciEff B.γ st.k) (ai + 1) (unapplied ai ce) := by
    rw [hun]
    refine ⟨hdvn, fun γn h => ⟨?_, (hdvs γn h).2⟩⟩
    have hc0 := (hdvs γn h).1
    have hai1 : uint.Z (ai + 1) = uint.Z ai + 1 := by word
    rw [hai1]
    rcases HJ with h1 | ⟨-, h2⟩
    · rw [h1]
      have : (0 : Int) ≤ A.length := by omega
      omega
    · omega
  have hms : ce = [] ∨ (entriesFrom (ai + 1) ce ∧ uint.Z (ai + 1) ≤ uint.Z ai + 1) := by
    by_cases hne : ce = []
    · left; exact hne
    · right
      obtain ⟨h1, h2⟩ := srvIdxOk_batch_from C.ai₀ ai A ce hidx Hai0 hne
      exact ⟨h1, by omega⟩
  ihave #Hbw' : iprop(batchWaitOk C.ρ B.E ce) $$ []
  · rw [batchWaitOk_beSucc HB]
    iunfold batchWaitOk at Hbw
    iunfold batchWaitOk
    imodintro
    iintro %m %hm
    iapply Hbw
    ipureintro; exact List.mem_append_right A hm
  ihave #Hsrv2 := Hsrv
  iunfold isServerM at Hsrv2
  icases Hsrv2 with ⟨%Hρr, -⟩
  iunfold kvRunAtOn at Hkr
  icases Hkr with ⟨Hka, %Hkc⟩
  ihave #Hkb : iprop(kvBatch C.γr (ciEff B.γ st.k) ai A ce) $$ []
  · iunfold kvBatch
    isplitr
    · rw [← Hρr]; iexact Hlbr
    ipureintro
    refine ⟨by rw [Hkc.2]; exact Hai0, fun m hm => ?_⟩
    rw [Hkc.1]; exact hcong m hm
  -- (D19i part 1) the floor past the batch, at its last index (`srvIdxOk_batch_last`)
  have e1 : (max (uint.Z ai) (((ce.getLast?).map (fun m => uint.Z m.index)).getD 0)).toNat =
      uint.nat C.ai₀ + (A ++ ce).length := by
    rw [srvIdxOk_batch_last C.ai₀ ai A ce hidx Hai0]; word
  have e2 : uint.nat ai + 1 = uint.nat C.ai₀ + A.length + 1 := by word
  ihave #Hracc' : rnAdvChan rac (letI := srvStor (GF := GF) C.ρ.raft.raft
      iprop(nodeAppliedLb C.ρ.raft.raft.cl nk
        (max (uint.Z ai) (((ce.getLast?).map (fun m => uint.Z m.index)).getD 0)).toNat ∗ nodeCommitLb C.ρ.raft.raft.cl nk
        (max (uint.Z ai) (((ce.getLast?).map (fun m => uint.Z m.index)).getD 0)).toNat ∗
        srvFrozenRange C.γs (uint.nat ai + 1)
          ((max (uint.Z ai) (((ce.getLast?).map (fun m => uint.Z m.index)).getD 0)).toNat + 1) ∗
        srvFrozenTerms C.γs 1 (A ++ ce))) $$ []
  · rw [e1, e2]; iExactEq Hracc; rw [ha00]
  ihave #HWc' : iprop(srvWTPool B.E C.wt) $$ []
  · rw [srvWTPool_beSucc HB]; iexact HWc
  ihave Hbr : iprop(srvBemuReaderAt C.s B.E.γbe) $$ [Hbr]
  · rw [beSucc_γbe HB]; iexact Hbr
  iapply (hAA C.s B.γ C.ci B.TM B.E C.ρ C.γr B.b C.ep apL es ceL ce (ai + 1) rac nc st ai at' a t cs x A
      C.ms C.γs C.wt dv γnc w nk γa sa (1 : Qp).half γn rt (rnLogOf γn (A ++ ce)).length (by rw [beSucc_authMode HB]; exact hM) hRB hms hb1 Hloop hok' hdv (by have := uint_nat_eq C.ai₀; omega) Hlt
      hdisk Hci hcia hγn (by rw [hun]; simp [rnLogOf]))
    $$ [Hai Hat Hcs Hcv Hss Hst Hbe Happ Hlr Hwr Htok Hbr HKV Hao Hka HRS Hnrc Hdv HAR HtokR Hrh Hwal Hso]
  · rw [hun]
    iframe Hsd Hmsinv HKVf Hwal Hrtf Hrtok
    iframe HWc' Hracc' Hcv Hkb Hbw' HWA Hlog Hsrv Hlnil Hbc Hents Hesl Hncb Hnc Hsn Hrac Hes Hsa Hpkg
    iframe
    iunfold srvGoRes
    iframe
    iexact Hdvr
  inext
  iintro ⟨%γ', %TM', %E', %b', %st', %ai', %at'', %a', %t', %cs', %HB', Hrh, #Hsrv', HAR, Hai, Hat, Hcs, #Hcv', Hss, Hst, HtokR, Hbe, Happ, Hlr, Hgr, Hbr, Hao,
      #Hlb, #HWA', ⟨%x', %sa', HKV, %Hx', #Hlog', Hka, HRS⟩, #HKVf', Hwal, Hso, %Hpost⟩
  obtain ⟨hloop', hai', hci', hciN, hat'⟩ := Hpost
  iunfold srvGoRes at Hgr
  icases Hgr with ⟨Hwr, Htok⟩
  iapply HΦ
  iunfold schedule.schedRunning
  iframe Hrt Htok Hrh
  ihave Hkr : iprop(kvRunAtOn C.γr C.ai₀ C.c₀ (A ++ ce) x' sa') $$ [Hka]
  · iunfold kvRunAtOn
    isplitl [Hka]
    · iapply (show kvAppliedOn (GF := GF) C.γr.raft C.γr.kv srvAuthSt0 (A ++ unapplied ai ce) x' sa' ⊢
        kvAppliedOn C.γr.raft C.γr.kv srvAuthSt0 (A ++ ce) x' sa' from by rw [hun]) $$ Hka
    ipureintro; exact Hkc
  ihave HRS : iprop(srvRest E' C.γr (A ++ ce)) $$ [HRS]
  · iapply (show srvRest (GF := GF) E' C.γr (A ++ unapplied ai ce) ⊢ srvRest E' C.γr (A ++ ce)
      from by rw [hun]) $$ HRS
  ihave HAR : iprop(srvApRes C.s C.γr (A ++ ce)) $$ [HAR]
  · iapply (show srvApRes (GF := GF) C.s C.γr (A ++ unapplied ai ce) ⊢ srvApRes C.s C.γr (A ++ ce)
      from by rw [hun]) $$ HAR
  ihave Hbr : iprop(srvBemuReaderAt C.s C.E.γbe) $$ [Hbr]
  · rw [← beSucc_γbe HB]; iexact Hbr
  iunfold applyResOn
  rw [hw]
  iexists ⟨γ', TM', E', b'⟩, st', ai', at'', a', t', cs', x', sa'
  isplitr
  · ipureintro; exact beSucc_trans HB HB'
  iframe Hsrv'
  ihave #Hcv'' : epCsAt C.ρ.raft (A ++ ce) cs' $$ []
  · rw [show A ++ ce = A ++ unapplied ai ce by rw [hun]]; iexact Hcv'
  iframe Hcv'' HKVf'
  iframe
  iframe Hlog'
  have hlast := srvIdxOk_batch_last C.ai₀ ai A ce hidx Hai0
  isplitr
  · iexists w + (unapplied ai ce).length
    iexact HWA'
  ipureintro
  rw [hun] at Hx'
  refine ⟨hloop', by rw [hai', hlast], ?_, hciN Hci, ?_⟩
  · apply ciJ_step _ _ _ ai ai' HJ (by rw [hai']; omega) hci'
  · rw [hun] at hat'; exact lastTermIs_append Hlt hat'


set_option hygiene false in
/-- `updateLeadership`'s last step: the stats (`BecomeLeader` unless nil), and the return. -/
local macro "ul_stats" : tactic => `(tactic| (
  (try wp_auto)
  by_cases hst : v.stats = null
  · rw [hst]
    (try wp_auto)
    iapply HΦ'
    itrivial
  · (try wp_auto)
    rw [decide_eq_false hst]
    (try wp_auto)
    wp_apply hBL v.stats $$ []
    · iframe #; ipureintro; exact hst
    (try wp_auto)
    iapply HΦ'
    itrivial))

set_option hygiene false in
/-- `updateLeadership`'s tail: the leader-change notification (if a new leader), the stats. -/
local macro "ul_tail" : tactic => `(tactic| (
  (try wp_auto)
  cases nl
  · ul_stats
  · (try wp_auto)
    wp_apply hN v.leaderChanged $$ []
    · iframe #
    ul_stats))

set_option maxHeartbeats 0 in
theorem EtcdServer.run.wp_proof
    (hAA : EtcdServer.applyAll.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hGI : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (hGT : raftpb.SnapshotMetadata.GetTerm.spec (GF := GF) (hG := hG))
    (hFifo : schedule.NewFIFOScheduler.spec (GF := GF) (hG := hG))
    (hGL : EtcdServer.getLead.spec (GF := GF) (hG := hG))
    (hSL : EtcdServer.setLead.spec (GF := GF) (hG := hG))
    (hIL : EtcdServer.isLeader.spec (GF := GF) (hG := hG))
    (hN : notify.Notifier.Notify.spec (GF := GF) (hG := hG))
    (hBL : v2stats.ServerStats.BecomeLeader.spec (GF := GF) (hG := hG))
    (hGCI : EtcdServer.getCommittedIndex.spec (GF := GF) (hG := hG))
    (hSCI : EtcdServer.setCommittedIndex.spec (GF := GF) (hG := hG))
    (hRS : raftNode.start.spec (GF := GF) (hG := hG))
    (hRA : raftNode.apply.spec (GF := GF) (hG := hG))
    (hNJ : schedule.NewJob.spec (GF := GF) (hG := hG))
    (hSch : schedule.Scheduler.Schedule.spec (GF := GF) (hG := hG)) :
    EtcdServer.run.spec (GF := GF) (hG := hG) := by
  intro s γ ci TM E ρ γr Er γn γg γcx γd v b ai₀ at₀ c₀ x₀
  wp_start as Hpre
  iunfold isServerRun at Hpre
  iNamed Hpre
  obtain ⟨HEC, HEγr, Hc0a⟩ := HEr
  icases HWB with ⟨%γp, #HWB, #HWA0⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsrv' := Hsrv
  iunfold isServer at Hsrv'
  icases Hsrv' with ⟨%Hrd, #Hsci, ⟨%fv, #Hfv⟩, #Hat, -⟩
  ihave #Hfv' := Hfv
  iunfold srvFieldsAt at Hfv'
  icases Hfv' with ⟨#Hlgf, %Hslgnn, #Hw, #Hwok, %HE, %HEo, #Hhook, #Hlv, #Hlok, #Hfc, #Has,
    #Hcl, #Hrc, #Hq, #Hlgmu, #Hmid, #Hlead, #Het, #Htm, #Hnot, #Halm⟩
  ihave #Hrf' := Hrf
  iunfold srvRunFieldsAt at Hrf'
  icases Hrf' with ⟨#Hecf, ⟨%γe, #Hecb⟩, #Hscf, #Hscb, #Hdcf, #Hcff, #Hcfs, #Hcpf, #Hcpok, #Hstf,
    #Hlcf, #Hlcn, #Hltg, #Hcinv, #Hgok⟩
  ihave #Hrn' := Hrn
  iunfold isRaftNode at Hrn'
  iNamed Hrn'
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule $$ []
  · iPkgInit
  ihave #Hrpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_apply hLg s fv.lg $$ [Hlr] as ⟨%Hlg0, Hlr⟩
  · iframe Hlgf; iframe Hlr; ipureintro; exact Hslgnn
  (try wp_auto)
  -- `s.r.raftStorage.Snapshot()`: the snapshot the server started from
  icases Hsnap with ⟨%ms', #Hms', Hsnap⟩
  icombine Hms Hms' gives %Hmseq
  subst Hmseq
  wp_bind (App (Val (ms @!! go.GoType.PointerType go_etcd_io.raft.v3.MemoryStorage.ty @!! go!"Snapshot"))
    (Val #()))
  iunfold rnSnapOnce at Hsnap
  iapply Hsnap
  inext
  iintro %sn %pm0 %cs0 %sv %Hsv #Hsn #Hpm0 #Hcs0' #Hcsok Hnone #Hmsinv
  -- (2026-10-31, #11) the snapshot's disk side, from the construction's bundle and the node
  icases Hsnapb with ⟨%γt, #Hsro⟩
  ihave #Hsd : srvSnapDisk s γr $$ []
  · iapply srvSnapDisk_of_RO s ci E γr γt Er γn
    iframe Hsro Hrn
  -- (2026-10-30, the repair) the storage's stored snapshot index at least `0`
  imod memSnapNone_open γn.γs $$ Hnone with #Hslb0
  obtain ⟨Hsvi, Hsvt, Hpm0n, Hcs0n⟩ := Hsv
  -- the snapshot (raft's `ownSnapM`, read-only: nothing writes it), opened to its metadata `md`
  -- and the metadata's conf state `cs`, which `run` reads directly (the index and term through
  -- the getters, over the metadata's `smOpt`); the pointers are the allocated ones the
  -- contract names (stage R8b: until then non-nil by the conf state having a voter)
  ihave #Hsn' := Hsn
  iunfold ownSnapM at Hsn'
  icases Hsn' with ⟨%ds, %md, %uf, %Hsn0, #HD, #Hd, #HM, #Hm, #Hpb⟩
  icombine HM Hpm0 gives %Hpmeq
  subst Hpmeq
  ihave #Hm' := Hm
  iunfold smOpt at Hm'
  icases Hm' with (⟨%Hmdn, %Hmd0⟩ | #Hm')
  · exfalso; exact Hpm0n Hmdn
  iunfold smPts at Hm'
  icases Hm' with ⟨%cs, %pi, %pt, %uf', %Hmd0, #HC, #Hc, #HI, #HcI, #HT, #HcT, #Hpb'⟩
  icombine HC Hcs0' gives %Hcseq
  subst Hcseq
  have Hcs0 : cs ≠ null := Hcs0n
  (try wp_auto)
  -- the FIFO scheduler: its stop token, its queue `[n₀, p₀]` (`p₀` saving `True`)
  wp_apply hFifo fv.lg iprop(True) $$ [] as %sc ⟨%γs, %n₀, %p₀, #Hfifo, Hstoptok, Hq, #Hp0, -⟩
  · ipureintro; exact Hlg0
  ihave #Hfifo' := Hfifo
  iunfold schedule.isFifo at Hfifo'
  icases Hfifo' with ⟨%Hscnn, -⟩
  cases sc with
  | nil => exact absurd rfl Hscnn
  | ok sci =>
  (try wp_auto)
  -- the ready handler
  wp_func_lits
  (try wp_auto)
  ipersist s
  iStructNamedSuffix «$r0» "R"
  iclear _R
  irename getLeadR => getLead
  irename updateLeadR => updateLead
  irename updateLeadershipR => updateLeadership
  irename updateCommittedIndexR => updateCommittedIndex
  ipersist getLead
  ipersist updateLead
  ipersist updateLeadership
  ipersist updateCommittedIndex
  ihave #Hrh : iprop(isReadyHandler «$r0_ptr» (∃ c : w64, srvCommittedOwn γr c) γr) $$ []
  · iunfold isReadyHandler
    iexists _, _, _, _
    iframe getLead updateLead updateLeadership updateCommittedIndex
    isplitr
    · -- `getLead`
      iintro !> %Φ' !> - HΦ'
      wp_auto
      wp_apply hGL s $$ [] as %ld -
      · iframe Hlead
      (try wp_auto)
      iapply HΦ'
      itrivial
    isplitr
    · -- `updateLead`
      iintro %ld !> %Φ' !> - HΦ'
      wp_auto
      wp_apply hSL s ld $$ []
      · iframe Hlead
      (try wp_auto)
      iapply HΦ'
      itrivial
    isplitr
    · -- `updateLeadership`
      iintro %nl !> %Φ' !> - HΦ'
      wp_auto
      wp_apply hIL s fv.memberID $$ [] as %isl -
      · iframe Hlead Hmid
      (try wp_auto)
      ihave #Hlok' := Hlok
      ihave #Hcpok' := Hcpok
      iunfold compactorOk at Hcpok'
      iunfold lessorOk at Hlok'
      icases Hlok' with ⟨%li, %Hli, -, #HDemote, -⟩
      ihave #Pnot : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.notify $$ []
      · iPkgInit
      ihave #Pst : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats $$ []
      · iPkgInit
      ihave #Pt : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
      · iPkgInit
      -- `if !s.isLeader() { .. } else { .. }`, joined (`wp_join`, it only reads `newLeader`): the
      -- notification and the stats after it (`ul_tail`) are verified once
      wp_join at next with [newLeader]
      · cases isl
        · -- not the leader: `Demote`, `Pause`
          simp only [Bool.not_false]
          (try wp_auto)
          rw [Hli]
          (try wp_auto)
          wp_apply HDemote
          (try wp_auto)
          -- `if s.compactor != nil { s.compactor.Pause() }` (M2, S4: a compactor's `Pause`)
          icases Hcpok' with (%Hcpn | ⟨%T, %P, #Hcp⟩)
          · rw [Hcpn]
            (try wp_auto)
            wp_join_done
          icases v3compactor.compactorOk_Pause _ _ _ $$ Hcp with ⟨%ci, %Hci, #HPause⟩
          rw [Hci]
          (try wp_auto)
          wp_apply HPause
          (try wp_auto)
          wp_join_done
        · -- the leader: the election time (if new), `Resume`
          simp only [Bool.not_true]
          (try wp_auto)
          wp_join at next with [newLeader]
          · cases nl
            · (try wp_auto)
              wp_join_done
            · (try wp_auto)
              wp_apply time.wp_Now as %tn -
              (try wp_auto)
              wp_apply sync.RWMutex.wp_Lock_guard (srvLeadTimeMuAddr s) (leadTimeP s) $$ [] as ⟨Hwl, HP⟩
              · iframe Hltg
              iunfold leadTimeP at HP
              icases HP with ⟨%t0, Hlt⟩
              (try wp_auto)
              wp_apply sync.RWMutex.wp_Unlock_guard (srvLeadTimeMuAddr s) (leadTimeP s) $$ [Hwl Hlt]
              · iframe Hwl; iunfold leadTimeP; iexists _; iexact Hlt
              (try wp_auto)
              wp_join_done
          -- `if s.compactor != nil { s.compactor.Resume() }` (M2, S4: a compactor's `Resume`)
          icases Hcpok' with (%Hcpn | ⟨%T, %P, #Hcp⟩)
          · rw [Hcpn]
            (try wp_auto)
            wp_join_done
          icases v3compactor.compactorOk_Resume _ _ _ $$ Hcp with ⟨%ci, %Hci, #HResume⟩
          rw [Hci]
          (try wp_auto)
          wp_apply HResume
          (try wp_auto)
          wp_join_done
      ul_tail
    · -- `updateCommittedIndex`: the writer's half of the committed index
      iintro %ci' %Lc !> %Φ' !> ⟨⟨%c, Hown⟩, #HLc, %HciL⟩ HΦ'
      wp_auto
      wp_apply hGCI s γr (some c) $$ [Hown] as %cci ⟨-, Hown, %Hcci⟩
      · iframe Hcinv; iunfold srvCommittedOwnOpt; iexact Hown
      iunfold srvCommittedOwnOpt at Hown
      have hc : cci = c := Hcci c rfl
      subst hc
      (try wp_auto)
      wp_if_destruct
      · wp_apply hSCI s γr cci ci' Lc (by word) $$ [Hown] as ⟨Hown, #Hca⟩
        · iframe HLc Hcinv; iframe Hown; ipureintro; exact HciL
        (try wp_auto)
        iapply HΦ'
        iframe Hca
        iexists ci'; iexact Hown
      · iunfold srvCommittedOwn at Hown
        ihave #Hlb := monoNatLbOwn_get γr.committed _ _ $$ Hown
        ihave #Hca : iprop(committedAtLeast γr ci') $$ []
        · iapply committedAtLeast_le γr cci ci' (by word)
          iunfold committedAtLeast
          iexact Hlb
        (try wp_auto)
        iapply HΦ'
        iframe Hca
        iexists cci
        iunfold srvCommittedOwn
        iexact Hown
  -- `s.r.start(rh)`: the raft loop, owning the committed index's writer half
  ihave #Hmsinv0 : (letI : MemStorReg GF := ⟨γn.reg⟩; memStorInv γn.ms γn.γs γn.node.cl γn.key)
    $$ []
  · iExactEq Hmsinv; rw [← Hmsγ]
  wp_apply hRS Er γn (srvRAddr s) «$r0_ptr» [] (∃ c : w64, srvCommittedOwn γr c) Hdisk.2.2.2
    $$ [Hloop Hrdone Hcomm Hsend Hwtl]
  · rw [HEγr]; iframe Hrh Hrn Hmsinv0 Hslb0; iframe
  (try wp_auto)
  -- `ep`: the snapshot's conf state (the field `cs`, loaded), index and term (the getters, over
  -- the metadata's `smOpt`, read-only: `ai₀` and `at₀`)
  have hGI' := hGI md DFrac.discard sv.Metadata'
  rw [Hsvi] at hGI'
  have hGT' := hGT md DFrac.discard sv.Metadata'
  rw [Hsvt] at hGT'
  wp_apply hGI' $$ [] as -
  · iframe Hm
  (try wp_auto)
  wp_apply hGI' $$ [] as -
  · iframe Hm
  (try wp_auto)
  wp_apply hGT' $$ [] as -
  · iframe Hm
  (try wp_auto)
  wp_apply hGI' $$ [] as -
  · iframe Hm
  (try wp_auto)
  rw [decide_eq_false Hcs0]
  (try wp_auto)
  (try wp_func_lits)
  (try wp_auto)
  -- `expiredLeaseC`: the lessor is non-nil (`lessorOk`)
  ihave #Hlok' := Hlok
  iunfold lessorOk at Hlok'
  icases Hlok' with ⟨%li, %Hli, -, -, #HExp⟩
  rw [Hli]
  (try wp_auto)
  wp_apply HExp as %elc ⟨%γel, #Helc⟩
  (try wp_auto)
  -- the apply thread's resources at the empty log
  iStructNamedSuffix ep "E"
  iclear _E
  irename confStateE => confState
  irename diskSnapshotIndexE => diskSnapshotIndex
  irename memorySnapshotIndexE => memorySnapshotIndex
  irename appliedtE => appliedt
  irename appliediE => appliedi
  iunfold applyStart at Hstart
  icases Hstart with ⟨%st₀, %a₀, %t₀, %f₀, Hst, %Hst0, Hbe, Happ, Hlr', Hbr, Hwr, HKV, Hao,
    #Hlog0, Hkr, HRS, HAR, Hfs, Hso⟩
  obtain ⟨Hloop0, Hc0⟩ := Hst0
  -- (D19i part 1) the start index is the raft log's start (`kvRun`'s, `rnEnvOk`'s)
  iunfold kvRun at Hkr
  icases Hkr with ⟨Hka0, %Hkc0⟩
  ihave Hkr : kvRun γr ai₀ c₀ [] x₀ $$ [Hka0]
  · iunfold kvRun; iframe Hka0; ipureintro; exact Hkc0
  ihave #Henv' := Henv
  iunfold rnEnvOk at Henv'
  icases Henv' with ⟨-, %Hnm, %Hmd, -⟩
  have Hpre0 : uint.Z ai₀ = (γn.pre.length : Int) := by
    rw [← Hkc0.2, ← HEγr]; exact Hnm.2.2
  ihave HR0 : iprop(applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ []) $$
      [appliedi appliedt confState diskSnapshotIndex memorySnapshotIndex Hfs Hst Hbe Happ Hlr' Hbr Hwr
        HKV Hao Hkr HRS HAR Hwth Hso]
  · iunfold applyRes
    iexists ⟨γ, TM, E, b⟩, st₀, ai₀, at₀, a₀, t₀, cs, x₀
    isplitr
    · ipureintro; exact beSucc_refl γ E
    iframe Hsrv
    -- (D19i part 1) `ep.confState`'s first value, read-only; the snapshot token
    ihave confState : epConfState ep_ptr cs $$ [confState]
    · iunfold epConfState; iframe confState Hcsok
    ihave #Hcv0 : epCsAt ρ.raft [] cs $$ []
    · iunfold epCsAt; ileft; ipureintro; rfl
    iframe Hcv0 Hkvf Hso
    iframe
    isplitl
    · iunfold srvSnapState; rw [← Hmsγ]; iexists ai₀, ai₀, f₀; iframe
      simp only
      isplitr
      · ipureintro; exact ⟨Int.le_refl _, Int.le_refl _⟩
      isplitr
      · iexact Hms
      iExactEq Hslb0; rfl
    iframe Hlog0
    isplitr
    · iexists uint.nat ai₀
      rw [← srvWTAt_taken]
      iexact HWA0
    ipureintro
    refine ⟨Hloop0, by simp, Or.inl Hc0.symm, ?_, Or.inl rfl⟩
    rw [← Hc0, Hc0a.2.2]; have := uint_nat_eq c₀; word
  -- the loop: the log `A` received, the scheduler's queue ending with the name of `Q`, the last
  -- tracked job's `Post` (the initial `True` before the first job) and the resource `R` the next
  -- job gets from `run` (`applyRes []` before the first job), together `applyRes A`
  ihave HI : iprop(∃ (A : List EntryModel) (Ps : List GName) (pl : GName) (Q R : IProp GF),
      "Happly" ∷ rnApplyTok γn A ∗ "Hq" ∷ schedule.schedQueue γs (Ps ++ [pl]) ∗
      "#Hpl" ∷ schedule.savedProp pl Q ∗ "HR" ∷ R ∗
      "#HQR" ∷ □ (Q ∗ R -∗ applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ A ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half))) $$ [Happly Hq HR0 Hrunh]
  · iexists [], [n₀], p₀, iprop(True), iprop(applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ [] ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half))
    simp only [List.cons_append, List.nil_append, List.length_nil, Nat.sub_zero]
    iframe
    iframe Hp0
    isplitl [HR0 Hrunh]
    · iunfold named
      isplitl [HR0]
      · iexact HR0
      iExactEq Hrunh; rfl
    iintro !> ⟨-, H⟩
    iexact H
  wp_for
  icases HI with ⟨%A, %Ps, %pl, %Q, %R, Happly, Hq, #Hpl, HR, #HQR⟩
  wp_apply (lc := 2) hRA Er γn (srvRAddr s) $$ [] as %apc #Hapc
  · iframe Hrn
  (try wp_auto)
  ihave #Hapc' := Hapc
  iunfold isRNApplyc at Hapc'
  ihave #Hapch : isChan apc γn.ap.chanName toApply $$ []
  · unfold isSpsc; icases Hapc' with ⟨$, -⟩
  wp_apply_core chan.wp_select_blocking
  -- `ap := <-s.r.apply()`: a batch `ce` after `A`, scheduled
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists toApply, inferInstance, inferInstance, inferInstance, inferInstance, apc, γn.ap.chanName
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact Hapch
    iunfold rnApplyTok at Happly
    icases Happly with ⟨%rcv, Hcons, #Hidx⟩
    iapply spsc_rcv_au γn.ap apc _ _ rcv _ $$ Hapc' [$Hlc1 $Hlc2] Hcons
    inext
    iintro %apv %ok Hrecv
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hrecv with ⟨Hf, -⟩
      iexfalso; iexact Hf
    simp only [↓reduceIte]
    icases Hrecv with ⟨HP, Hcons⟩
    icases rnApplyTok_recv Er γn rcv A apv $$ Hcons Hidx HP with
      (⟨%ce, %ceL, Happly, #Hents, #Hentsat, #HC, %Hsnap, Hnc, HG, #Hrac, #Hcl, #Hrtok⟩ | Hsnp)
    rotate_left
    · -- (J8b, 2026-11-01) a snapshot payload's job (`rnApSnap`): `applyAll` over `specSnap`
      -- (`run_job_snap`), scheduled as a batch's
      icases Hsnp with ⟨%A', %sv, Happly, %Hlen, #Hes, #Hsn, #Hcert, #Hloc, #HC, Hnc, #Hrac, #Hcl,
        #Hrtok⟩
      obtain ⟨hlt, hlenA, h61, hboot⟩ := Hlen
      icases Hnc with ⟨%γnc, #Hncb, Hnrc⟩
      have hρ : ρ.raft = Er.γr.raft := by rw [HEγr, ← Hrd]
      have hρC : ρ.raft = γr.raft := by rw [hρ, HEγr]
      have hnd0 : ρ.raft.raft = γn.node := by rw [hρ, Hnm.1]
      have hgn : γn.node = γr.raft.raft := by rw [← hnd0, hρC]
      have hp0 : γn.pre = [] := Hc0a.2.1
      have ha0 : uint.nat ai₀ = 0 := by rw [Hc0a.2.2]; rfl
      ihave #HC' : iprop(srvC ρ E ai₀ c₀ x₀ A') $$ []
      · rw [← HEC]; iexact HC
      (try wp_auto)
      wp_func_lits
      (try wp_auto)
      ipersist ap
      ihave #Hapf := ap
      iStructNamedSuffix Hapf "A"
      ihave #HC'' := HC'
      iunfold srvC at HC''
      icases HC'' with ⟨-, -, #Hlbr⟩
      imod (schedule.savedProp_alloc iprop(applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ A' ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half)))
        with ⟨%post, #Hpost⟩
      wp_apply hNJ γs _ _ iprop(R ∗ notifyRcvN γnc 0) Q
          iprop(applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ A' ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half)) $$ [] as %j #Hj
      · iframe #
        iunfold schedule.jobFnSpec
        iintro !> %ctx %cd !> %Φj ⟨Hrun, ⟨HR', Hnrc⟩, HQ, -, -⟩ HΦj
        ihave ⟨Hres, Hhalf⟩ := HQR $$ [HQ HR']
        · iframe
        wp_auto
        wp_bind (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyAll"))
          (Val #ep_ptr)) (Val #ap_ptr))
        iapply (run_job_snap hAA.2 ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ A A' ap_ptr apv.entries' apv.snapshot' sv
          apv.raftAdvancedC' apv.notifyc' γs γnc γn apv.raftTerm' ha0 Hc0a.1 hp0 hgn hρC
          (by rw [← hρC, hρ]; exact Hnm.2.1) rfl rfl hlt hlenA h61 hboot Hslg) $$ [Hrun Hres Hnrc]
        · iframe #
          iframe Hrun Hres Hnrc
        inext
        iintro ⟨Hrun, Hres⟩
        wp_auto
        iapply HΦj
        iframe
      wp_apply hSch sci γs j iprop(R ∗ notifyRcvN γnc 0) Q
          iprop(applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ A' ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half)) (some (Ps, pl, post))
        $$ [HR Hnrc Hq] as Hq
      · iframe #
        iframe
        simp only [schedule.schedPre]
        iframe #
        iunfold named at Hq
        iexact Hq
      simp only [schedule.schedPost]
      (try wp_auto)
      wp_for_post
      iframe
      iexists A', Ps ++ [pl], post, iprop(applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ A' ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half)), iprop(True)
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      iframe
      iframe #
      iunfold named
      iintro !> ⟨H, -⟩
      iexact H
    -- (D43 M3) `notifyc` and the driver's view, at the apply side (`rnDv`)
    icases Hnc with ⟨%γnc, #Hncb0, Hnrc⟩
    have hρ : ρ.raft = Er.γr.raft := by rw [HEγr, ← Hrd]
    have hpre : γn.pre = ρ.raft.pre := by rw [hρ]; exact Hnm.2.1.symm
    have hnd0 : ρ.raft.raft = γn.node := by rw [hρ, Hnm.1]
    ihave #Hncb : isNotify γnc apv.notifyc' (dvView ρ.raft (rnDv γn ce) (A ++ ce)) $$ []
    · rw [← rnApR_dv γn ρ.raft hpre hnd0 A ce]; iexact Hncb0
    ihave #Hdyn := srvRaftNodeCC_of_isRaftNode Er γn s $$ Hrn
    icases rnApGive_dv s γn ρ.raft hpre hnd0 A ce $$ [Hdyn HG] with ⟨Hdv, #Hdvr⟩
    · iframe Hdyn HG
    have hdvn : rnDv γn ce = none → ∀ m, m ∈ ce → m.typ ≠ W32 1 := by
      intro h
      unfold rnDv at h
      by_cases hh : rnHands γn ce
      · rw [ite_eq_left hh] at h; cases h
      unfold rnHands at hh
      simp only [Bool.not_eq_true] at hh
      intro m hm hty
      unfold ccIn at hh
      have := List.any_eq_false.1 hh m hm
      simp [hty] at this
    have hdvs : ∀ γn', rnDv γn ce = some γn' → uint.Z c₀ ≤ uint.Z ai₀ ∧
        ρ.raft.raft.rule = srvRule γr.kv.c0 ρ.raft.raft.boot ∧
        ρ.raft.pre = [] ∧ ρ.raft.ai0 = W64 0 := by
      intro γn' _
      obtain ⟨hc, hp0, ha0⟩ := Hc0a
      refine ⟨hc, ?_, by rw [← hpre]; exact hp0, ?_⟩
      · rw [hnd0, Hmd, HEγr]
      · rw [hρ, HEγr, Hkc0.2]; exact ha0
    ihave #HC' : iprop(srvC ρ E ai₀ c₀ x₀ (A ++ ce)) $$ []
    · rw [← HEC]; iexact HC
    (try wp_auto)
    wp_func_lits
    (try wp_auto)
    -- `ap`'s fields, read-only from here on
    ipersist ap
    ihave #Hapf := ap
    iStructNamedSuffix Hapf "A"
    ihave #HC'' := HC'
    iunfold srvC at HC''
    icases HC'' with ⟨%Hcp, #Hbw, #Hlbr⟩
    obtain ⟨hidx, hok⟩ := Hcp
    ihave #Hbc : iprop(batchCommittedIdx γr ce) $$ []
    · rw [← HEγr]
      iapply batchCommittedIdx_of_last Er.γr ai₀ A ce hidx $$ Hcl
    imod (schedule.savedProp_alloc iprop(applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ (A ++ ce) ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half)))
      with ⟨%post, #Hpost⟩
    wp_apply hNJ γs _ _ iprop(R ∗ notifyRcv γnc ∗ dvView ρ.raft (rnDv γn ce) A) Q
        iprop(applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ (A ++ ce) ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half)) $$ [] as %j #Hj
    · iframe #
      iunfold schedule.jobFnSpec
      iintro !> %ctx %cd !> %Φj ⟨Hrun, ⟨HR', Hnrc, Hdv⟩, HQ, -, -⟩ HΦj
      ihave ⟨Hres, Hhalf⟩ := HQR $$ [HQ HR']
      · iframe
      icases srvRunH_lend γn ρ.raft hnd0 ce $$ Hhalf with ⟨Hrh, Hrhb⟩
      wp_auto
      wp_bind (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyAll"))
        (Val #ep_ptr)) (Val #ap_ptr))
      have hp0 : γn.pre = [] := Hc0a.2.1
      have ha0 : uint.nat ai₀ = 0 := by rw [Hc0a.2.2]; rfl
      ihave #Hrac' : rnAdvChan apv.raftAdvancedC' (letI := srvStor (GF := GF) ρ.raft.raft
          iprop(nodeAppliedLb ρ.raft.raft.cl γn.key (uint.nat ai₀ + (A ++ ce).length) ∗ nodeCommitLb ρ.raft.raft.cl γn.key (uint.nat ai₀ + (A ++ ce).length) ∗
            srvFrozenRange γn.γs (uint.nat ai₀ + A.length + 1)
              (uint.nat ai₀ + (A ++ ce).length + 1) ∗
            srvFrozenTerms γn.γs (uint.nat ai₀ + 1) (A ++ ce))) $$ []
      · rw [hnd0, show uint.nat ai₀ + (A ++ ce).length = (γn.pre ++ A ++ ce).length by
            simp [hp0, ha0],
          show uint.nat ai₀ + A.length + 1 = (γn.pre ++ A).length + 1 by simp [hp0, ha0],
          show uint.nat ai₀ + 1 = γn.pre.length + 1 by simp [hp0, ha0]]
        iexact Hrac
      have hgn : γr.raft.raft = γn.node := by rw [← HEγr, ← hρ]; exact hnd0
      have hJ := run_job_body hAA.1 ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ A ce ap_ptr
        apv.entries' ceL apv.raftAdvancedC' apv.notifyc' γs (rnDv γn ce) γnc hidx hok rfl hdvn hdvs
        γn.key ha0 Hdisk γn apv.raftTerm' hgn.symm Hc0a.1
      ihave #Hmsinv' : (letI : MemStorReg GF := ⟨γr.raft.raft.reg⟩;
          memStorInv γn.ms γn.γs γr.raft.raft.cl γn.key) $$ []
      · iExactEq Hmsinv; rw [hgn, ← Hmsγ]
      simp only [run_job_body_match] at hJ
      iapply hJ $$ [Hrun Hres Hnrc Hdv Hrh]
      · iframe #
        iframe Hrun Hres Hnrc Hdv Hrh
        rw [← Hsnap]; iexact snapshotA
      inext
      iintro ⟨Hrun, Hres, Hrh⟩
      ihave Hhalf := Hrhb $$ Hrh
      wp_auto
      iapply HΦj
      iframe
    -- `sched.Schedule(f)`, tracked: `Q` the job's `Prev`, its `Post` saved as `post`
    wp_apply hSch sci γs j iprop(R ∗ notifyRcv γnc ∗ dvView ρ.raft (rnDv γn ce) A) Q
        iprop(applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ (A ++ ce) ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half)) (some (Ps, pl, post))
      $$ [HR Hnrc Hdv Hq] as Hq
    · iframe #
      iframe
      simp only [schedule.schedPre]
      iframe #
      iunfold named at Hq
      iexact Hq
    simp only [schedule.schedPost]
    (try wp_auto)
    wp_for_post
    iframe
    iexists (A ++ ce), Ps ++ [pl], post,
      iprop(applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ (A ++ ce) ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half)), iprop(True)
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    iframe
    iframe #
    iunfold named
    iintro !> ⟨H, -⟩
    iexact H
  -- `leases := <-expiredLeaseC`: nothing is sent on it (D19n, D19q: the workload's grant guard
  -- holds of no lease, `lessorOk`'s `noGrant`, so no lease is granted and none expires);
  -- `revokeExpiredLeases` is never reached
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists GoSlice, inferInstance, inferInstance, inferInstance, inferInstance, elc, γel
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Helc
    iapply bag_recv_au γel elc _ _ $$ [$Hlc1 $Hlc2] Helc
    inext
    iintro %ls Hf
    iexfalso; iexact Hf
  -- `err := <-s.errorc`: nothing is sent on it (D19m: `apply` never asks `stopWithDelay` to
  -- stop the server, the transport has no peer that reports this member removed)
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, v.errorc, γe
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hecb
    iapply bag_recv_au γe v.errorc _ _ $$ [$Hlc1 $Hlc2] Hecb
    inext
    iintro %err Hf
    iexfalso; iexact Hf
  -- `<-s.stop`: nothing is sent on it (D19m: no `Stop`/`HardStop` in the runs covered); so `run`
  -- never returns, and its deferred shutdown (`Cleanup` among it) is never reached
  iapply BigAndL.bigAndL_cons.2
  isplit
  · icases Hscb with ⟨%γst, #Hstb⟩
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, v.stop, γst
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hstb
    iapply bag_recv_au γst v.stop _ _ $$ [$Hlc1 $Hlc2] Hstb
    inext
    iintro %u Hf
    iexfalso; iexact Hf
  iapply BigAndL.bigAndL_nil.2
  itrivial


set_option maxHeartbeats 0 in
/-- **`run.specOn`** (the auth plan's E3q): `wp_proof` with the jobs over `run_job_bodyOn`. -/
theorem EtcdServer.run.wp_proofOn
    (hAA : EtcdServer.applyAll.specOn (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hGI : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (hGT : raftpb.SnapshotMetadata.GetTerm.spec (GF := GF) (hG := hG))
    (hFifo : schedule.NewFIFOScheduler.spec (GF := GF) (hG := hG))
    (hGL : EtcdServer.getLead.spec (GF := GF) (hG := hG))
    (hSL : EtcdServer.setLead.spec (GF := GF) (hG := hG))
    (hIL : EtcdServer.isLeader.spec (GF := GF) (hG := hG))
    (hN : notify.Notifier.Notify.spec (GF := GF) (hG := hG))
    (hBL : v2stats.ServerStats.BecomeLeader.spec (GF := GF) (hG := hG))
    (hGCI : EtcdServer.getCommittedIndex.spec (GF := GF) (hG := hG))
    (hSCI : EtcdServer.setCommittedIndex.spec (GF := GF) (hG := hG))
    (hRS : raftNode.start.spec (GF := GF) (hG := hG))
    (hRA : raftNode.apply.spec (GF := GF) (hG := hG))
    (hNJ : schedule.NewJob.spec (GF := GF) (hG := hG))
    (hSch : schedule.Scheduler.Schedule.spec (GF := GF) (hG := hG)) :
    EtcdServer.run.specOn (GF := GF) (hG := hG) := by
  intro s γ ci TM E ρ γr Er γn γg γcx γd v b ai₀ at₀ c₀ x₀ γa hM hRB
  wp_start as Hpre
  iunfold isServerRunOn at Hpre
  iNamed Hpre
  obtain ⟨HEC, HEγr, Hc0a⟩ := HEr
  icases HWB with ⟨%γp, #HWB, #HWA0⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsrv' := Hsrv
  iunfold isServerM at Hsrv'
  icases Hsrv' with ⟨%Hrd, #Hsci, ⟨%fv, #Hfv⟩, #Hat, -⟩
  ihave #Hfv' := Hfv
  iunfold srvFieldsAtM at Hfv'
  icases Hfv' with ⟨#Hlgf, %Hslgnn, #Hw, #Hwok, %HE, %HEo, #Hhook, #Hlv, #Hlok, #Hfc, #Has,
    #Hcl, #Hrc, #Hq, #Hlgmu, #Hmid, #Hlead, #Het, #Htm, #Hnot, #Halm⟩
  ihave #Hrf' := Hrf
  iunfold srvRunFieldsAt at Hrf'
  icases Hrf' with ⟨#Hecf, ⟨%γe, #Hecb⟩, #Hscf, #Hscb, #Hdcf, #Hcff, #Hcfs, #Hcpf, #Hcpok, #Hstf,
    #Hlcf, #Hlcn, #Hltg, #Hcinv, #Hgok⟩
  ihave #Hrn' := Hrn
  iunfold isRaftNode at Hrn'
  iNamed Hrn'
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule $$ []
  · iPkgInit
  ihave #Hrpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_apply hLg s fv.lg $$ [Hlr] as ⟨%Hlg0, Hlr⟩
  · iframe Hlgf; iframe Hlr; ipureintro; exact Hslgnn
  (try wp_auto)
  -- `s.r.raftStorage.Snapshot()`: the snapshot the server started from
  icases Hsnap with ⟨%ms', #Hms', Hsnap⟩
  icombine Hms Hms' gives %Hmseq
  subst Hmseq
  wp_bind (App (Val (ms @!! go.GoType.PointerType go_etcd_io.raft.v3.MemoryStorage.ty @!! go!"Snapshot"))
    (Val #()))
  iunfold rnSnapOnce at Hsnap
  iapply Hsnap
  inext
  iintro %sn %pm0 %cs0 %sv %Hsv #Hsn #Hpm0 #Hcs0' #Hcsok Hnone #Hmsinv
  -- (2026-10-31, #11) the snapshot's disk side, from the construction's bundle and the node
  icases Hsnapb with ⟨%γt, #Hsro⟩
  ihave #Hsd : srvSnapDisk s γr $$ []
  · iapply srvSnapDisk_of_RO s ci E γr γt Er γn
    iframe Hsro Hrn
  -- (2026-10-30, the repair) the storage's stored snapshot index at least `0`
  imod memSnapNone_open γn.γs $$ Hnone with #Hslb0
  obtain ⟨Hsvi, Hsvt, Hpm0n, Hcs0n⟩ := Hsv
  -- the snapshot (raft's `ownSnapM`, read-only: nothing writes it), opened to its metadata `md`
  -- and the metadata's conf state `cs`, which `run` reads directly (the index and term through
  -- the getters, over the metadata's `smOpt`); the pointers are the allocated ones the
  -- contract names (stage R8b: until then non-nil by the conf state having a voter)
  ihave #Hsn' := Hsn
  iunfold ownSnapM at Hsn'
  icases Hsn' with ⟨%ds, %md, %uf, %Hsn0, #HD, #Hd, #HM, #Hm, #Hpb⟩
  icombine HM Hpm0 gives %Hpmeq
  subst Hpmeq
  ihave #Hm' := Hm
  iunfold smOpt at Hm'
  icases Hm' with (⟨%Hmdn, %Hmd0⟩ | #Hm')
  · exfalso; exact Hpm0n Hmdn
  iunfold smPts at Hm'
  icases Hm' with ⟨%cs, %pi, %pt, %uf', %Hmd0, #HC, #Hc, #HI, #HcI, #HT, #HcT, #Hpb'⟩
  icombine HC Hcs0' gives %Hcseq
  subst Hcseq
  have Hcs0 : cs ≠ null := Hcs0n
  (try wp_auto)
  -- the FIFO scheduler: its stop token, its queue `[n₀, p₀]` (`p₀` saving `True`)
  wp_apply hFifo fv.lg iprop(True) $$ [] as %sc ⟨%γs, %n₀, %p₀, #Hfifo, Hstoptok, Hq, #Hp0, -⟩
  · ipureintro; exact Hlg0
  ihave #Hfifo' := Hfifo
  iunfold schedule.isFifo at Hfifo'
  icases Hfifo' with ⟨%Hscnn, -⟩
  cases sc with
  | nil => exact absurd rfl Hscnn
  | ok sci =>
  (try wp_auto)
  -- the ready handler
  wp_func_lits
  (try wp_auto)
  ipersist s
  iStructNamedSuffix «$r0» "R"
  iclear _R
  irename getLeadR => getLead
  irename updateLeadR => updateLead
  irename updateLeadershipR => updateLeadership
  irename updateCommittedIndexR => updateCommittedIndex
  ipersist getLead
  ipersist updateLead
  ipersist updateLeadership
  ipersist updateCommittedIndex
  ihave #Hrh : iprop(isReadyHandler «$r0_ptr» (∃ c : w64, srvCommittedOwn γr c) γr) $$ []
  · iunfold isReadyHandler
    iexists _, _, _, _
    iframe getLead updateLead updateLeadership updateCommittedIndex
    isplitr
    · -- `getLead`
      iintro !> %Φ' !> - HΦ'
      wp_auto
      wp_apply hGL s $$ [] as %ld -
      · iframe Hlead
      (try wp_auto)
      iapply HΦ'
      itrivial
    isplitr
    · -- `updateLead`
      iintro %ld !> %Φ' !> - HΦ'
      wp_auto
      wp_apply hSL s ld $$ []
      · iframe Hlead
      (try wp_auto)
      iapply HΦ'
      itrivial
    isplitr
    · -- `updateLeadership`
      iintro %nl !> %Φ' !> - HΦ'
      wp_auto
      wp_apply hIL s fv.memberID $$ [] as %isl -
      · iframe Hlead Hmid
      (try wp_auto)
      ihave #Hlok' := Hlok
      ihave #Hcpok' := Hcpok
      iunfold compactorOk at Hcpok'
      iunfold lessorOk at Hlok'
      icases Hlok' with ⟨%li, %Hli, -, #HDemote, -⟩
      ihave #Pnot : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.notify $$ []
      · iPkgInit
      ihave #Pst : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats $$ []
      · iPkgInit
      ihave #Pt : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
      · iPkgInit
      -- `if !s.isLeader() { .. } else { .. }`, joined (`wp_join`, it only reads `newLeader`): the
      -- notification and the stats after it (`ul_tail`) are verified once
      wp_join at next with [newLeader]
      · cases isl
        · -- not the leader: `Demote`, `Pause`
          simp only [Bool.not_false]
          (try wp_auto)
          rw [Hli]
          (try wp_auto)
          wp_apply HDemote
          (try wp_auto)
          -- `if s.compactor != nil { s.compactor.Pause() }` (M2, S4: a compactor's `Pause`)
          icases Hcpok' with (%Hcpn | ⟨%T, %P, #Hcp⟩)
          · rw [Hcpn]
            (try wp_auto)
            wp_join_done
          icases v3compactor.compactorOk_Pause _ _ _ $$ Hcp with ⟨%ci, %Hci, #HPause⟩
          rw [Hci]
          (try wp_auto)
          wp_apply HPause
          (try wp_auto)
          wp_join_done
        · -- the leader: the election time (if new), `Resume`
          simp only [Bool.not_true]
          (try wp_auto)
          wp_join at next with [newLeader]
          · cases nl
            · (try wp_auto)
              wp_join_done
            · (try wp_auto)
              wp_apply time.wp_Now as %tn -
              (try wp_auto)
              wp_apply sync.RWMutex.wp_Lock_guard (srvLeadTimeMuAddr s) (leadTimeP s) $$ [] as ⟨Hwl, HP⟩
              · iframe Hltg
              iunfold leadTimeP at HP
              icases HP with ⟨%t0, Hlt⟩
              (try wp_auto)
              wp_apply sync.RWMutex.wp_Unlock_guard (srvLeadTimeMuAddr s) (leadTimeP s) $$ [Hwl Hlt]
              · iframe Hwl; iunfold leadTimeP; iexists _; iexact Hlt
              (try wp_auto)
              wp_join_done
          -- `if s.compactor != nil { s.compactor.Resume() }` (M2, S4: a compactor's `Resume`)
          icases Hcpok' with (%Hcpn | ⟨%T, %P, #Hcp⟩)
          · rw [Hcpn]
            (try wp_auto)
            wp_join_done
          icases v3compactor.compactorOk_Resume _ _ _ $$ Hcp with ⟨%ci, %Hci, #HResume⟩
          rw [Hci]
          (try wp_auto)
          wp_apply HResume
          (try wp_auto)
          wp_join_done
      ul_tail
    · -- `updateCommittedIndex`: the writer's half of the committed index
      iintro %ci' %Lc !> %Φ' !> ⟨⟨%c, Hown⟩, #HLc, %HciL⟩ HΦ'
      wp_auto
      wp_apply hGCI s γr (some c) $$ [Hown] as %cci ⟨-, Hown, %Hcci⟩
      · iframe Hcinv; iunfold srvCommittedOwnOpt; iexact Hown
      iunfold srvCommittedOwnOpt at Hown
      have hc : cci = c := Hcci c rfl
      subst hc
      (try wp_auto)
      wp_if_destruct
      · wp_apply hSCI s γr cci ci' Lc (by word) $$ [Hown] as ⟨Hown, #Hca⟩
        · iframe HLc Hcinv; iframe Hown; ipureintro; exact HciL
        (try wp_auto)
        iapply HΦ'
        iframe Hca
        iexists ci'; iexact Hown
      · iunfold srvCommittedOwn at Hown
        ihave #Hlb := monoNatLbOwn_get γr.committed _ _ $$ Hown
        ihave #Hca : iprop(committedAtLeast γr ci') $$ []
        · iapply committedAtLeast_le γr cci ci' (by word)
          iunfold committedAtLeast
          iexact Hlb
        (try wp_auto)
        iapply HΦ'
        iframe Hca
        iexists cci
        iunfold srvCommittedOwn
        iexact Hown
  -- `s.r.start(rh)`: the raft loop, owning the committed index's writer half
  ihave #Hmsinv0 : (letI : MemStorReg GF := ⟨γn.reg⟩; memStorInv γn.ms γn.γs γn.node.cl γn.key)
    $$ []
  · iExactEq Hmsinv; rw [← Hmsγ]
  wp_apply hRS Er γn (srvRAddr s) «$r0_ptr» [] (∃ c : w64, srvCommittedOwn γr c) Hdisk.2.2.2
    $$ [Hloop Hrdone Hcomm Hsend Hwtl]
  · rw [HEγr]; iframe Hrh Hrn Hmsinv0 Hslb0; iframe
  (try wp_auto)
  -- `ep`: the snapshot's conf state (the field `cs`, loaded), index and term (the getters, over
  -- the metadata's `smOpt`, read-only: `ai₀` and `at₀`)
  have hGI' := hGI md DFrac.discard sv.Metadata'
  rw [Hsvi] at hGI'
  have hGT' := hGT md DFrac.discard sv.Metadata'
  rw [Hsvt] at hGT'
  wp_apply hGI' $$ [] as -
  · iframe Hm
  (try wp_auto)
  wp_apply hGI' $$ [] as -
  · iframe Hm
  (try wp_auto)
  wp_apply hGT' $$ [] as -
  · iframe Hm
  (try wp_auto)
  wp_apply hGI' $$ [] as -
  · iframe Hm
  (try wp_auto)
  rw [decide_eq_false Hcs0]
  (try wp_auto)
  (try wp_func_lits)
  (try wp_auto)
  -- `expiredLeaseC`: the lessor is non-nil (`lessorOk`)
  ihave #Hlok' := Hlok
  iunfold lessorOk at Hlok'
  icases Hlok' with ⟨%li, %Hli, -, -, #HExp⟩
  rw [Hli]
  (try wp_auto)
  wp_apply HExp as %elc ⟨%γel, #Helc⟩
  (try wp_auto)
  -- the apply thread's resources at the empty log
  iStructNamedSuffix ep "E"
  iclear _E
  irename confStateE => confState
  irename diskSnapshotIndexE => diskSnapshotIndex
  irename memorySnapshotIndexE => memorySnapshotIndex
  irename appliedtE => appliedt
  irename appliediE => appliedi
  iunfold applyStartOn at Hstart
  icases Hstart with ⟨%st₀, %a₀, %t₀, %f₀, Hst, %Hst0, Hbe, Happ, Hlr', Hbr, Hwr, HKV, Hao,
    #Hlog0, Hkr, HRS, HAR, Hfs, HtokR, Hso⟩
  obtain ⟨Hloop0, Hc0⟩ := Hst0
  -- (D19i part 1) the start index is the raft log's start (`kvRun`'s, `rnEnvOk`'s)
  iunfold kvRunAtOn at Hkr
  icases Hkr with ⟨Hka0, %Hkc0⟩
  ihave Hkr : kvRunAtOn γr ai₀ c₀ [] x₀ srvAuthSt0 $$ [Hka0]
  · iunfold kvRunAtOn; iframe Hka0; ipureintro; exact Hkc0
  ihave #Henv' := Henv
  iunfold rnEnvOk at Henv'
  icases Henv' with ⟨-, %Hnm, %Hmd, -⟩
  have Hpre0 : uint.Z ai₀ = (γn.pre.length : Int) := by
    rw [← Hkc0.2, ← HEγr]; exact Hnm.2.2
  ihave HR0 : iprop(applyResOn ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ []) $$
      [appliedi appliedt confState diskSnapshotIndex memorySnapshotIndex Hfs Hst Hbe Happ Hlr' Hbr Hwr
        HKV Hao Hkr HRS HAR HtokR Hwth Hso]
  · iunfold applyResOn
    iexists ⟨γ, TM, E, b⟩, st₀, ai₀, at₀, a₀, t₀, cs, x₀, srvAuthSt0
    isplitr
    · ipureintro; exact beSucc_refl γ E
    iframe Hsrv
    -- (D19i part 1) `ep.confState`'s first value, read-only; the snapshot token
    ihave confState : epConfState ep_ptr cs $$ [confState]
    · iunfold epConfState; iframe confState Hcsok
    ihave #Hcv0 : epCsAt ρ.raft [] cs $$ []
    · iunfold epCsAt; ileft; ipureintro; rfl
    iframe Hcv0 Hkvf Hso
    iframe
    isplitl
    · iunfold srvSnapState; rw [← Hmsγ]; iexists ai₀, ai₀, f₀; iframe
      simp only
      isplitr
      · ipureintro; exact ⟨Int.le_refl _, Int.le_refl _⟩
      isplitr
      · iexact Hms
      iExactEq Hslb0; rfl
    iframe Hlog0
    isplitr
    · iexists uint.nat ai₀
      rw [← srvWTAt_taken]
      iexact HWA0
    ipureintro
    refine ⟨Hloop0, by simp, Or.inl Hc0.symm, ?_, Or.inl rfl⟩
    rw [← Hc0, Hc0a.2.2]; have := uint_nat_eq c₀; word
  -- the loop: the log `A` received, the scheduler's queue ending with the name of `Q`, the last
  -- tracked job's `Post` (the initial `True` before the first job) and the resource `R` the next
  -- job gets from `run` (`applyRes []` before the first job), together `applyRes A`
  ihave HI : iprop(∃ (A : List EntryModel) (Ps : List GName) (pl : GName) (Q R : IProp GF),
      "Happly" ∷ rnApplyTok γn A ∗ "Hq" ∷ schedule.schedQueue γs (Ps ++ [pl]) ∗
      "#Hpl" ∷ schedule.savedProp pl Q ∗ "HR" ∷ R ∗
      "#HQR" ∷ □ (Q ∗ R -∗ applyResOn ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ A ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half))) $$ [Happly Hq HR0 Hrunh]
  · iexists [], [n₀], p₀, iprop(True), iprop(applyResOn ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ [] ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half))
    simp only [List.cons_append, List.nil_append, List.length_nil, Nat.sub_zero]
    iframe
    iframe Hp0
    isplitl [HR0 Hrunh]
    · iunfold named
      isplitl [HR0]
      · iexact HR0
      iExactEq Hrunh; rfl
    iintro !> ⟨-, H⟩
    iexact H
  wp_for
  icases HI with ⟨%A, %Ps, %pl, %Q, %R, Happly, Hq, #Hpl, HR, #HQR⟩
  wp_apply (lc := 2) hRA Er γn (srvRAddr s) $$ [] as %apc #Hapc
  · iframe Hrn
  (try wp_auto)
  ihave #Hapc' := Hapc
  iunfold isRNApplyc at Hapc'
  ihave #Hapch : isChan apc γn.ap.chanName toApply $$ []
  · unfold isSpsc; icases Hapc' with ⟨$, -⟩
  wp_apply_core chan.wp_select_blocking
  -- `ap := <-s.r.apply()`: a batch `ce` after `A`, scheduled
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists toApply, inferInstance, inferInstance, inferInstance, inferInstance, apc, γn.ap.chanName
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact Hapch
    iunfold rnApplyTok at Happly
    icases Happly with ⟨%rcv, Hcons, #Hidx⟩
    iapply spsc_rcv_au γn.ap apc _ _ rcv _ $$ Hapc' [$Hlc1 $Hlc2] Hcons
    inext
    iintro %apv %ok Hrecv
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hrecv with ⟨Hf, -⟩
      iexfalso; iexact Hf
    simp only [↓reduceIte]
    icases Hrecv with ⟨HP, Hcons⟩
    icases rnApplyTok_recv Er γn rcv A apv $$ Hcons Hidx HP with
      (⟨%ce, %ceL, Happly, #Hents, #Hentsat, #HC, %Hsnap, Hnc, HG, #Hrac, #Hcl, #Hrtok⟩ | Hsnp)
    rotate_left
    · -- SNAPSHOT-SORRY: a snapshot payload's job (as `wp_proof`'s)
      sorry
    -- (D43 M3) `notifyc` and the driver's view, at the apply side (`rnDv`)
    icases Hnc with ⟨%γnc, #Hncb0, Hnrc⟩
    have hρ : ρ.raft = Er.γr.raft := by rw [HEγr, ← Hrd]
    have hpre : γn.pre = ρ.raft.pre := by rw [hρ]; exact Hnm.2.1.symm
    have hnd0 : ρ.raft.raft = γn.node := by rw [hρ, Hnm.1]
    ihave #Hncb : isNotify γnc apv.notifyc' (dvView ρ.raft (rnDv γn ce) (A ++ ce)) $$ []
    · rw [← rnApR_dv γn ρ.raft hpre hnd0 A ce]; iexact Hncb0
    ihave #Hdyn := srvRaftNodeCC_of_isRaftNode Er γn s $$ Hrn
    icases rnApGive_dv s γn ρ.raft hpre hnd0 A ce $$ [Hdyn HG] with ⟨Hdv, #Hdvr⟩
    · iframe Hdyn HG
    have hdvn : rnDv γn ce = none → ∀ m, m ∈ ce → m.typ ≠ W32 1 := by
      intro h
      unfold rnDv at h
      by_cases hh : rnHands γn ce
      · rw [ite_eq_left hh] at h; cases h
      unfold rnHands at hh
      simp only [Bool.not_eq_true] at hh
      intro m hm hty
      unfold ccIn at hh
      have := List.any_eq_false.1 hh m hm
      simp [hty] at this
    have hdvs : ∀ γn', rnDv γn ce = some γn' → uint.Z c₀ ≤ uint.Z ai₀ ∧
        ρ.raft.raft.rule = srvRule γr.kv.c0 ρ.raft.raft.boot ∧
        ρ.raft.pre = [] ∧ ρ.raft.ai0 = W64 0 := by
      intro γn' _
      obtain ⟨hc, hp0, ha0⟩ := Hc0a
      refine ⟨hc, ?_, by rw [← hpre]; exact hp0, ?_⟩
      · rw [hnd0, Hmd, HEγr]
      · rw [hρ, HEγr, Hkc0.2]; exact ha0
    ihave #HC' : iprop(srvCM true ρ E ai₀ c₀ x₀ (A ++ ce)) $$ []
    · rw [← HEC]; iexact HC
    (try wp_auto)
    wp_func_lits
    (try wp_auto)
    -- `ap`'s fields, read-only from here on
    ipersist ap
    ihave #Hapf := ap
    iStructNamedSuffix Hapf "A"
    ihave #HC'' := HC'
    iunfold srvCM at HC''
    icases HC'' with ⟨%Hcp, #Hbw, #Hlbr⟩
    obtain ⟨hidx, hok⟩ := Hcp
    ihave #Hbc : iprop(batchCommittedIdx γr ce) $$ []
    · rw [← HEγr]
      iapply batchCommittedIdx_of_last Er.γr ai₀ A ce hidx $$ Hcl
    imod (schedule.savedProp_alloc iprop(applyResOn ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ (A ++ ce) ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half)))
      with ⟨%post, #Hpost⟩
    wp_apply hNJ γs _ _ iprop(R ∗ notifyRcv γnc ∗ dvView ρ.raft (rnDv γn ce) A) Q
        iprop(applyResOn ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ (A ++ ce) ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half)) $$ [] as %j #Hj
    · iframe #
      iunfold schedule.jobFnSpec
      iintro !> %ctx %cd !> %Φj ⟨Hrun, ⟨HR', Hnrc, Hdv⟩, HQ, -, -⟩ HΦj
      ihave ⟨Hres, Hhalf⟩ := HQR $$ [HQ HR']
      · iframe
      icases srvRunH_lend γn ρ.raft hnd0 ce $$ Hhalf with ⟨Hrh, Hrhb⟩
      wp_auto
      wp_bind (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyAll"))
        (Val #ep_ptr)) (Val #ap_ptr))
      have hp0 : γn.pre = [] := Hc0a.2.1
      have ha0 : uint.nat ai₀ = 0 := by rw [Hc0a.2.2]; rfl
      ihave #Hrac' : rnAdvChan apv.raftAdvancedC' (letI := srvStor (GF := GF) ρ.raft.raft
          iprop(nodeAppliedLb ρ.raft.raft.cl γn.key (uint.nat ai₀ + (A ++ ce).length) ∗ nodeCommitLb ρ.raft.raft.cl γn.key (uint.nat ai₀ + (A ++ ce).length) ∗
            srvFrozenRange γn.γs (uint.nat ai₀ + A.length + 1)
              (uint.nat ai₀ + (A ++ ce).length + 1) ∗
            srvFrozenTerms γn.γs (uint.nat ai₀ + 1) (A ++ ce))) $$ []
      · rw [hnd0, show uint.nat ai₀ + (A ++ ce).length = (γn.pre ++ A ++ ce).length by
            simp [hp0, ha0],
          show uint.nat ai₀ + A.length + 1 = (γn.pre ++ A).length + 1 by simp [hp0, ha0],
          show uint.nat ai₀ + 1 = γn.pre.length + 1 by simp [hp0, ha0]]
        iexact Hrac
      have hgn : γr.raft.raft = γn.node := by rw [← HEγr, ← hρ]; exact hnd0
      have hJ := run_job_bodyOn hAA ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ A ce
        γa hM hRB ap_ptr
        apv.entries' ceL apv.raftAdvancedC' apv.notifyc' γs (rnDv γn ce) γnc hidx hok rfl hdvn hdvs
        γn.key ha0 Hdisk γn apv.raftTerm' hgn.symm Hc0a.1
      ihave #Hmsinv' : (letI : MemStorReg GF := ⟨γr.raft.raft.reg⟩;
          memStorInv γn.ms γn.γs γr.raft.raft.cl γn.key) $$ []
      · iExactEq Hmsinv; rw [hgn, ← Hmsγ]
      simp only [run_job_body_match] at hJ
      iapply hJ $$ [Hrun Hres Hnrc Hdv Hrh]
      · iframe #
        iframe Hrun Hres Hnrc Hdv Hrh
        rw [← Hsnap]; iexact snapshotA
      inext
      iintro ⟨Hrun, Hres, Hrh⟩
      ihave Hhalf := Hrhb $$ Hrh
      wp_auto
      iapply HΦj
      iframe
    -- `sched.Schedule(f)`, tracked: `Q` the job's `Prev`, its `Post` saved as `post`
    wp_apply hSch sci γs j iprop(R ∗ notifyRcv γnc ∗ dvView ρ.raft (rnDv γn ce) A) Q
        iprop(applyResOn ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ (A ++ ce) ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half)) (some (Ps, pl, post))
      $$ [HR Hnrc Hdv Hq] as Hq
    · iframe #
      iframe
      simp only [schedule.schedPre]
      iframe #
      iunfold named at Hq
      iexact Hq
    simp only [schedule.schedPost]
    (try wp_auto)
    wp_for_post
    iframe
    iexists (A ++ ce), Ps ++ [pl], post,
      iprop(applyResOn ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ (A ++ ce) ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half)), iprop(True)
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    iframe
    iframe #
    iunfold named
    iintro !> ⟨H, -⟩
    iexact H
  -- `leases := <-expiredLeaseC`: nothing is sent on it (D19n, D19q: the workload's grant guard
  -- holds of no lease, `lessorOk`'s `noGrant`, so no lease is granted and none expires);
  -- `revokeExpiredLeases` is never reached
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists GoSlice, inferInstance, inferInstance, inferInstance, inferInstance, elc, γel
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Helc
    iapply bag_recv_au γel elc _ _ $$ [$Hlc1 $Hlc2] Helc
    inext
    iintro %ls Hf
    iexfalso; iexact Hf
  -- `err := <-s.errorc`: nothing is sent on it (D19m: `apply` never asks `stopWithDelay` to
  -- stop the server, the transport has no peer that reports this member removed)
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, v.errorc, γe
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hecb
    iapply bag_recv_au γe v.errorc _ _ $$ [$Hlc1 $Hlc2] Hecb
    inext
    iintro %err Hf
    iexfalso; iexact Hf
  -- `<-s.stop`: nothing is sent on it (D19m: no `Stop`/`HardStop` in the runs covered); so `run`
  -- never returns, and its deferred shutdown (`Cleanup` among it) is never reached
  iapply BigAndL.bigAndL_cons.2
  isplit
  · icases Hscb with ⟨%γst, #Hstb⟩
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, v.stop, γst
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hstb
    iapply bag_recv_au γst v.stop _ _ $$ [$Hlc1 $Hlc2] Hstb
    inext
    iintro %u Hf
    iexfalso; iexact Hf
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
