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
theorem run_job_body (hAA : EtcdServer.applyAll.spec (GF := GF) (hG := hG))
    (C : ApplyCtx GF) (A ce : List EntryModel)
    (apL : Loc) (es : GoSlice) (ceL : List Loc) (rac nc : GoChan) (γs : schedule.SchedNames)
    (dv : Option Loc) (γnc : NotifyNames)
    (hidx : srvIdxOk C.ai₀ (A ++ ce)) (hok : logShape (A ++ ce))
    (hw : C.γw = C.ρ.wait)
    -- (D43 M3, 2026-10-25) the driver's view, `applyAll`'s (`dvOk`): without one, raft's static
    -- mode or no conf entry; with one, a fresh start (`c₀ ≤ ai₀`) at the server's decoder
    (hdvn : dv = none → C.ρ.raft.raft.dyn = false ∨ ∀ m, m ∈ ce → m.typ ≠ W32 1)
    (hdvs : ∀ γn, dv = some γn → uint.Z C.c₀ ≤ uint.Z C.ai₀ ∧ C.ρ.raft.raft.dyn = true ∧
      C.ρ.raft.raft.dec = srvDec C.γr.kv.c0 C.ρ.raft.raft.boot ∧ C.ρ.raft.pre = [] ∧
      C.ρ.raft.ai0 = W64 0) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerApplyAll C.s C.γr ∗ batchWaitOk C.ρ C.E (A ++ ce) ∗
        taEntriesAddr apL ↦□ es ∗ taRaftAdvancedCAddr apL ↦□ rac ∗
        rnAdvChan rac (memFloorAtLeast C.ms C.γs (uint.Z C.ai₀ + ((A ++ ce).length : Int))) ∗
        taSnapshotAddr apL ↦□ (null : Loc) ∗ taNotifycAddr apL ↦□ nc ∗
        isNotify γnc nc (dvView C.ρ.raft dv (A ++ ce)) ∗ notifyRcv γnc ∗
        dvView C.ρ.raft dv A ∗ dvRes C.s C.ρ.raft dv (A ++ ce) ∗
        es ↦*□ ceL ∗ entriesAt ceL ce ∗ batchCommittedIdx C.γr ce ∗ schedule.schedRunning γs ∗
        applyRes C A ∗ srvWTPool C.E C.wt ∗ srvRLogLb C.ρ.raft (A ++ ce) }}
      (App (App (Val (C.s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyAll")) (Val #C.ep))
        (Val #apL))
    {{ RET #(); schedule.schedRunning γs ∗ applyRes C (A ++ ce) }} := by
  iintro %Φ ⟨#Hpkg, #Hsa, #Hbw, #Hes, #Hrac, #Hracc, #Hsn, #Hnc, #Hncb, Hnrc, Hdv, #Hdvr, #Hesl,
    #Hents, #Hbc, Hrun, HR, #HWc, #Hlbr⟩ HΦ
  iunfold applyRes at HR
  icases HR with ⟨%B, %st, %ai, %at', %a, %t, %cs, %x, %HB, #Hsrv, Hai, Hat, Hcs, Hss, Hst, Hbe, Happ, Hlr, Hbr,
    Hwr, HKV, Hao, #Hlog, Hkr, HRS, HAR, ⟨%w, #HWA, %Hw⟩, %Hpure⟩
  rw [hw]
  obtain ⟨Hloop, Hai0, HJ, Hstep, Hcap, Hlt⟩ := Hpure
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
  ihave #Hracc' : rnAdvChan rac (memFloorAtLeast C.ms C.γs
      (max (uint.Z ai) (((ce.getLast?).map (fun m => uint.Z m.index)).getD 0))) $$ []
  · rw [srvIdxOk_batch_last C.ai₀ ai A ce hidx Hai0]; iexact Hracc
  ihave #HWc' : iprop(srvWTPool B.E C.wt) $$ []
  · rw [srvWTPool_beSucc HB]; iexact HWc
  ihave Hbr : iprop(srvBemuReaderAt C.s B.E.γbe) $$ [Hbr]
  · rw [beSucc_γbe HB]; iexact Hbr
  iapply (hAA C.s B.γ C.ci B.TM B.E C.ρ C.γr B.b C.ep apL es ceL ce (ai + 1) rac nc st ai at' a t cs x A
      C.ms C.γs C.wt dv γnc w hms hb1 Hloop hok' Hcap hdv Hw)
    $$ [Hai Hat Hcs Hss Hst Hbe Happ Hlr Hwr Htok Hbr HKV Hao Hka HRS Hnrc Hdv HAR]
  · rw [hun]
    iframe HWc' Hracc' Hkb Hbw' HWA Hlog Hsrv Hbc Hents Hesl Hncb Hnc Hsn Hrac Hes Hsa Hpkg
    iframe
    iunfold srvGoRes
    iframe
    iexact Hdvr
  inext
  iintro ⟨%γ', %TM', %E', %b', %st', %ai', %at'', %a', %t', %cs', %HB', #Hsrv', HAR, Hai, Hat, Hcs, Hss, Hst, Hbe, Happ, Hlr, Hgr, Hbr, Hao,
      #Hlb, #HWA', ⟨%x', HKV, %Hx', #Hlog', Hka, HRS⟩, %Hpost⟩
  obtain ⟨hloop', hai', hci', hat'⟩ := Hpost
  iunfold srvGoRes at Hgr
  icases Hgr with ⟨Hwr, Htok⟩
  iapply HΦ
  iunfold schedule.schedRunning
  iframe Hrt Htok
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
  iframe
  iframe Hlog'
  have hlast := srvIdxOk_batch_last C.ai₀ ai A ce hidx Hai0
  isplitr
  · iexists w + (unapplied ai ce).length
    iframe HWA'
    ipureintro
    rw [hun, hai', hlast, List.length_append]
    push_cast
    omega
  ipureintro
  rw [hun] at Hx'
  refine ⟨hloop', by rw [hai', hlast], ?_, ?_, Hcap, ?_⟩
  · apply ciJ_step _ _ _ ai ai' HJ (by rw [hai']; omega) hci'
  · exact entriesStep_append' C.c₀ A ce C.x₀ x x' Hstep (entriesStep_congr _ _ ce hcong x x' Hx')
  · rw [hun] at hat'; exact lastTermIs_append Hlt hat'

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
    -- (D43 M3, 2026-10-25) the driver's view, `applyAll`'s (`dvOk`): without one, raft's static
    -- mode or no conf entry; with one, a fresh start (`c₀ ≤ ai₀`) at the server's decoder
    (hdvn : dv = none → C.ρ.raft.raft.dyn = false ∨ ∀ m, m ∈ ce → m.typ ≠ W32 1)
    (hdvs : ∀ γn, dv = some γn → uint.Z C.c₀ ≤ uint.Z C.ai₀ ∧ C.ρ.raft.raft.dyn = true ∧
      C.ρ.raft.raft.dec = srvDec C.γr.kv.c0 C.ρ.raft.raft.boot ∧ C.ρ.raft.pre = [] ∧
      C.ρ.raft.ai0 = W64 0) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        srvLessorNil C.s ∗ isServerApplyAll C.s C.γr ∗ batchWaitOk C.ρ C.E (A ++ ce) ∗
        taEntriesAddr apL ↦□ es ∗ taRaftAdvancedCAddr apL ↦□ rac ∗
        rnAdvChan rac (memFloorAtLeast C.ms C.γs (uint.Z C.ai₀ + ((A ++ ce).length : Int))) ∗
        taSnapshotAddr apL ↦□ (null : Loc) ∗ taNotifycAddr apL ↦□ nc ∗
        isNotify γnc nc (dvView C.ρ.raft dv (A ++ ce)) ∗ notifyRcv γnc ∗
        dvView C.ρ.raft dv A ∗ dvRes C.s C.ρ.raft dv (A ++ ce) ∗
        es ↦*□ ceL ∗ entriesAt ceL ce ∗ batchCommittedIdx C.γr ce ∗ schedule.schedRunning γs ∗
        applyResOn C A ∗ srvWTPool C.E C.wt ∗ srvRLogLb C.ρ.raft (A ++ ce) }}
      (App (App (Val (C.s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyAll")) (Val #C.ep))
        (Val #apL))
    {{ RET #(); schedule.schedRunning γs ∗ applyResOn C (A ++ ce) }} := by
  iintro %Φ ⟨#Hpkg, #Hlnil, #Hsa, #Hbw, #Hes, #Hrac, #Hracc, #Hsn, #Hnc, #Hncb, Hnrc, Hdv, #Hdvr, #Hesl,
    #Hents, #Hbc, Hrun, HR, #HWc, #Hlbr⟩ HΦ
  iunfold applyResOn at HR
  icases HR with ⟨%B, %st, %ai, %at', %a, %t, %cs, %x, %sa, %HB, #Hsrv, Hai, Hat, Hcs, Hss, Hst, Hbe, Happ, Hlr, Hbr,
    Hwr, HKV, Hao, #Hlog, Hkr, HRS, HAR, ⟨%w, #HWA, %Hw⟩, HtokR, %Hpure⟩
  rw [hw]
  obtain ⟨Hloop, Hai0, HJ, Hstep, Hcap, Hlt⟩ := Hpure
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
  ihave #Hracc' : rnAdvChan rac (memFloorAtLeast C.ms C.γs
      (max (uint.Z ai) (((ce.getLast?).map (fun m => uint.Z m.index)).getD 0))) $$ []
  · rw [srvIdxOk_batch_last C.ai₀ ai A ce hidx Hai0]; iexact Hracc
  ihave #HWc' : iprop(srvWTPool B.E C.wt) $$ []
  · rw [srvWTPool_beSucc HB]; iexact HWc
  ihave Hbr : iprop(srvBemuReaderAt C.s B.E.γbe) $$ [Hbr]
  · rw [beSucc_γbe HB]; iexact Hbr
  iapply (hAA C.s B.γ C.ci B.TM B.E C.ρ C.γr B.b C.ep apL es ceL ce (ai + 1) rac nc st ai at' a t cs x A
      C.ms C.γs C.wt dv γnc w γa sa (by rw [beSucc_authMode HB]; exact hM) hRB hms hb1 Hloop hok' Hcap hdv Hw)
    $$ [Hai Hat Hcs Hss Hst Hbe Happ Hlr Hwr Htok Hbr HKV Hao Hka HRS Hnrc Hdv HAR HtokR]
  · rw [hun]
    iframe HWc' Hracc' Hkb Hbw' HWA Hlog Hsrv Hlnil Hbc Hents Hesl Hncb Hnc Hsn Hrac Hes Hsa Hpkg
    iframe
    iunfold srvGoRes
    iframe
    iexact Hdvr
  inext
  iintro ⟨%γ', %TM', %E', %b', %st', %ai', %at'', %a', %t', %cs', %HB', #Hsrv', HAR, Hai, Hat, Hcs, Hss, Hst, HtokR, Hbe, Happ, Hlr, Hgr, Hbr, Hao,
      #Hlb, #HWA', ⟨%x', %sa', HKV, %Hx', #Hlog', Hka, HRS⟩, %Hpost⟩
  obtain ⟨hloop', hai', hci', hat'⟩ := Hpost
  iunfold srvGoRes at Hgr
  icases Hgr with ⟨Hwr, Htok⟩
  iapply HΦ
  iunfold schedule.schedRunning
  iframe Hrt Htok
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
  iframe
  iframe Hlog'
  have hlast := srvIdxOk_batch_last C.ai₀ ai A ce hidx Hai0
  isplitr
  · iexists w + (unapplied ai ce).length
    iframe HWA'
    ipureintro
    rw [hun, hai', hlast, List.length_append]
    push_cast
    omega
  ipureintro
  rw [hun] at Hx'
  refine ⟨hloop', by rw [hai', hlast], ?_, ?_, Hcap, ?_⟩
  · apply ciJ_step _ _ _ ai ai' HJ (by rw [hai']; omega) hci'
  · exact entriesStep_append' C.c₀ A ce C.x₀ x x' Hstep (entriesStep_congr _ _ ce hcong x x' Hx')
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
  iintro %sn %pm0 %cs0 %sv %Hsv #Hsn #Hpm0 #Hcs0' #Hcsok ⟨%σ0, Htok0, %Hσ0⟩
  -- (D22 J4) the token shared from here on: raft's goroutine (`s.r.start`, next) and the apply
  -- job both use it
  imod srvStorTok_alloc _ _ σ0 ⊤ Hσ0 $$ Htok0 with ⟨#Hro0, Hak0, %γss0, #Htinv0, #Hslb0⟩
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
  wp_apply hFifo fv.lg $$ [] as %sc ⟨%γs, %n₀, %p₀, #Hfifo, Hstoptok, Hq, #Hp0⟩
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
          icases Hcpok' with %Hcpn
          rw [Hcpn]
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
          icases Hcpok' with %Hcpn
          rw [Hcpn]
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
  wp_apply hRS Er γn (srvRAddr s) «$r0_ptr» [] (∃ c : w64, srvCommittedOwn γr c)
    $$ [Hloop Hrdone Hcomm Hsend]
  · rw [HEγr]; iframe Hrh Hrn; iframe
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
    #Hlog0, Hkr, HRS, HAR, Hfs⟩
  obtain ⟨Hloop0, Hc0⟩ := Hst0
  -- (D19i part 1) the start index is the raft log's start (`kvRun`'s, `rnEnvOk`'s)
  iunfold kvRun at Hkr
  icases Hkr with ⟨Hka0, %Hkc0⟩
  ihave Hkr : kvRun γr ai₀ c₀ [] x₀ $$ [Hka0]
  · iunfold kvRun; iframe Hka0; ipureintro; exact Hkc0
  ihave #Henv' := Henv
  iunfold rnEnvOk at Henv'
  icases Henv' with ⟨-, %Hnm, %Hmd, %Hcap0, -⟩
  have Hpre0 : uint.Z ai₀ = (γn.pre.length : Int) := by
    rw [← Hkc0.2, ← HEγr]; exact Hnm.2.2
  ihave HR0 : iprop(applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ []) $$
      [appliedi appliedt confState diskSnapshotIndex memorySnapshotIndex Hfs Hst Hbe Happ Hlr' Hbr Hwr
        HKV Hao Hkr HRS HAR Hak0]
  · iunfold applyRes
    iexists ⟨γ, TM, E, b⟩, st₀, ai₀, at₀, a₀, t₀, cs, x₀
    isplitr
    · ipureintro; exact beSucc_refl γ E
    iframe Hsrv
    -- (D19i part 1) `ep.confState`'s first value, read-only; the snapshot token
    ihave confState : epConfState ep_ptr cs $$ [confState]
    · iunfold epConfState; iframe confState Hcsok
    iframe
    isplitl
    · iunfold srvSnapState; rw [← Hmsγ]; iexists ai₀, ai₀, f₀; iframe
      simp only
      isplitr
      · ipureintro; exact ⟨Int.le_refl _, Int.le_refl _⟩
      isplitr
      · iexact Hms
      iframe Hro0
      iexists γss0
      iframe Htinv0
      iapply monoNatLbOwn_le (uint.nat (W64 0)) (by simp) $$ Hslb0
    iframe Hlog0
    isplitr
    · iexists uint.nat ai₀
      rw [← srvWTAt_taken]
      iframe HWA0
      ipureintro; have := uint_nat_eq ai₀; omega
    ipureintro
    refine ⟨Hloop0, by simp, Or.inl Hc0.symm, rfl, Hcap0, Or.inl rfl⟩
  -- the loop: the log `A` received, the scheduler's queue ending with the name of `Q`, the last
  -- tracked job's `Post` (the initial `True` before the first job) and the resource `R` the next
  -- job gets from `run` (`applyRes []` before the first job), together `applyRes A`
  ihave HI : iprop(∃ (A : List EntryModel) (Ps : List GName) (pl : GName) (Q R : IProp GF),
      "Happly" ∷ rnApplyTok γn A ∗ "Hq" ∷ schedule.schedQueue γs (Ps ++ [pl]) ∗
      "#Hpl" ∷ schedule.savedProp pl Q ∗ "HR" ∷ R ∗
      "#HQR" ∷ □ (Q ∗ R -∗ applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ A)) $$ [Happly Hq HR0]
  · iexists [], [n₀], p₀, iprop(True), iprop(applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ [])
    simp only [List.cons_append, List.nil_append, List.length_nil, Nat.sub_zero]
    iframe
    iframe Hp0
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
      ⟨%ce, %ceL, Happly, #Hents, #Hentsat, #HC, %Hsnap, Hnc, HG, #Hrac, #Hcl⟩
    -- (D43 M3) `notifyc` and the driver's view, at the apply side (`rnDv`)
    icases Hnc with ⟨%γnc, #Hncb0, Hnrc⟩
    have hρ : ρ.raft = Er.γr.raft := by rw [HEγr, ← Hrd]
    have hpre : γn.pre = ρ.raft.pre := by rw [hρ]; exact Hnm.2.1.symm
    have hnd0 : ρ.raft.raft = γn.node := by rw [hρ, Hnm.1]
    ihave #Hncb : isNotify γnc apv.notifyc' (dvView ρ.raft (rnDv γn ce) (A ++ ce)) $$ []
    · rw [← rnApR_dv γn ρ.raft hpre hnd0 A ce]; iexact Hncb0
    ihave #Hdyn := srvRaftNodeDyn_of_isRaftNode Er γn s $$ Hrn
    icases rnApGive_dv s γn ρ.raft hpre hnd0 A ce $$ [Hdyn HG] with ⟨Hdv, #Hdvr⟩
    · iframe Hdyn HG
    have hdvn : rnDv γn ce = none → ρ.raft.raft.dyn = false ∨ ∀ m, m ∈ ce → m.typ ≠ W32 1 := by
      intro h
      unfold rnDv at h
      by_cases hh : rnHands γn ce
      · rw [ite_eq_left hh] at h; cases h
      unfold rnHands at hh
      cases hd : γn.node.dyn
      · left
        rw [hρ, Hnm.1]
        exact hd
      · right
        rw [hd] at hh
        simp only [Bool.true_and, Bool.not_eq_true] at hh
        intro m hm hty
        unfold ccIn at hh
        have := List.any_eq_false.1 hh m hm
        simp [hty] at this
    have hdvs : ∀ γn', rnDv γn ce = some γn' → uint.Z c₀ ≤ uint.Z ai₀ ∧
        ρ.raft.raft.dyn = true ∧ ρ.raft.raft.dec = srvDec γr.kv.c0 ρ.raft.raft.boot ∧
        ρ.raft.pre = [] ∧ ρ.raft.ai0 = W64 0 := by
      intro γn' h
      unfold rnDv at h
      by_cases hh : rnHands γn ce
      · have hd : γn.node.dyn = true := by
          unfold rnHands at hh; simp only [Bool.and_eq_true] at hh; exact hh.1
        obtain ⟨hc, hp0, ha0⟩ := Hc0a hd
        have hnd : ρ.raft.raft = γn.node := by rw [hρ, Hnm.1]
        refine ⟨hc, by rw [hnd]; exact hd, ?_, by rw [← hpre]; exact hp0, ?_⟩
        · rw [hnd, Hmd hd, HEγr]
        · rw [hρ, HEγr, Hkc0.2]; exact ha0
      · rw [ite_eq_right hh] at h; cases h
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
    imod (schedule.savedProp_alloc (applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ (A ++ ce)))
      with ⟨%post, #Hpost⟩
    wp_apply hNJ γs _ _ iprop(R ∗ notifyRcv γnc ∗ dvView ρ.raft (rnDv γn ce) A) Q
        iprop(applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ (A ++ ce)) $$ [] as %j #Hj
    · iframe #
      iunfold schedule.jobFnSpec
      iintro !> %ctx %cd !> %Φj ⟨Hrun, ⟨HR', Hnrc, Hdv⟩, HQ, -⟩ HΦj
      ihave Hres := HQR $$ [HQ HR']
      · iframe
      wp_auto
      wp_bind (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyAll"))
        (Val #ep_ptr)) (Val #ap_ptr))
      ihave #Hrac' : rnAdvChan apv.raftAdvancedC'
          (memFloorAtLeast γn.ms γn.γs (uint.Z ai₀ + ((A ++ ce).length : Int))) $$ []
      · rw [show uint.Z ai₀ + ((A ++ ce).length : Int) = ((γn.pre ++ A ++ ce).length : Int) by
          simp only [List.length_append]; push_cast; omega]
        iexact Hrac
      iapply (run_job_body hAA ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ A ce ap_ptr
        apv.entries' ceL apv.raftAdvancedC' apv.notifyc' γs (rnDv γn ce) γnc hidx hok rfl hdvn hdvs)
        $$ [Hrun Hres Hnrc Hdv]
      · iframe #
        iframe Hrun Hres Hnrc Hdv
        rw [← Hsnap]; iexact snapshotA
      inext
      iintro ⟨Hrun, Hres⟩
      wp_auto
      iapply HΦj
      iframe
    -- `sched.Schedule(f)`, tracked: `Q` the job's `Prev`, its `Post` saved as `post`
    wp_apply hSch sci γs j iprop(R ∗ notifyRcv γnc ∗ dvView ρ.raft (rnDv γn ce) A) Q
        iprop(applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ (A ++ ce)) (some (Ps, pl, post))
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
      iprop(applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ (A ++ ce)), iprop(True)
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
    icases Hf with ⟨%id, Hf⟩
    iunfold srvGrantGuard at Hf
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
  iintro %sn %pm0 %cs0 %sv %Hsv #Hsn #Hpm0 #Hcs0' #Hcsok ⟨%σ0, Htok0, %Hσ0⟩
  -- (D22 J4) the token shared from here on: raft's goroutine (`s.r.start`, next) and the apply
  -- job both use it
  imod srvStorTok_alloc _ _ σ0 ⊤ Hσ0 $$ Htok0 with ⟨#Hro0, Hak0, %γss0, #Htinv0, #Hslb0⟩
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
  wp_apply hFifo fv.lg $$ [] as %sc ⟨%γs, %n₀, %p₀, #Hfifo, Hstoptok, Hq, #Hp0⟩
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
          icases Hcpok' with %Hcpn
          rw [Hcpn]
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
          icases Hcpok' with %Hcpn
          rw [Hcpn]
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
  wp_apply hRS Er γn (srvRAddr s) «$r0_ptr» [] (∃ c : w64, srvCommittedOwn γr c)
    $$ [Hloop Hrdone Hcomm Hsend]
  · rw [HEγr]; iframe Hrh Hrn; iframe
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
    #Hlog0, Hkr, HRS, HAR, Hfs, HtokR⟩
  obtain ⟨Hloop0, Hc0⟩ := Hst0
  -- (D19i part 1) the start index is the raft log's start (`kvRun`'s, `rnEnvOk`'s)
  iunfold kvRunAtOn at Hkr
  icases Hkr with ⟨Hka0, %Hkc0⟩
  ihave Hkr : kvRunAtOn γr ai₀ c₀ [] x₀ srvAuthSt0 $$ [Hka0]
  · iunfold kvRunAtOn; iframe Hka0; ipureintro; exact Hkc0
  ihave #Henv' := Henv
  iunfold rnEnvOk at Henv'
  icases Henv' with ⟨-, %Hnm, %Hmd, %Hcap0, -⟩
  have Hpre0 : uint.Z ai₀ = (γn.pre.length : Int) := by
    rw [← Hkc0.2, ← HEγr]; exact Hnm.2.2
  ihave HR0 : iprop(applyResOn ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ []) $$
      [appliedi appliedt confState diskSnapshotIndex memorySnapshotIndex Hfs Hst Hbe Happ Hlr' Hbr Hwr
        HKV Hao Hkr HRS HAR Hak0 HtokR]
  · iunfold applyResOn
    iexists ⟨γ, TM, E, b⟩, st₀, ai₀, at₀, a₀, t₀, cs, x₀, srvAuthSt0
    isplitr
    · ipureintro; exact beSucc_refl γ E
    iframe Hsrv
    -- (D19i part 1) `ep.confState`'s first value, read-only; the snapshot token
    ihave confState : epConfState ep_ptr cs $$ [confState]
    · iunfold epConfState; iframe confState Hcsok
    iframe
    isplitl
    · iunfold srvSnapState; rw [← Hmsγ]; iexists ai₀, ai₀, f₀; iframe
      simp only
      isplitr
      · ipureintro; exact ⟨Int.le_refl _, Int.le_refl _⟩
      isplitr
      · iexact Hms
      iframe Hro0
      iexists γss0
      iframe Htinv0
      iapply monoNatLbOwn_le (uint.nat (W64 0)) (by simp) $$ Hslb0
    iframe Hlog0
    isplitr
    · iexists uint.nat ai₀
      rw [← srvWTAt_taken]
      iframe HWA0
      ipureintro; have := uint_nat_eq ai₀; omega
    ipureintro
    refine ⟨Hloop0, by simp, Or.inl Hc0.symm, rfl, Hcap0, Or.inl rfl⟩
  -- the loop: the log `A` received, the scheduler's queue ending with the name of `Q`, the last
  -- tracked job's `Post` (the initial `True` before the first job) and the resource `R` the next
  -- job gets from `run` (`applyRes []` before the first job), together `applyRes A`
  ihave HI : iprop(∃ (A : List EntryModel) (Ps : List GName) (pl : GName) (Q R : IProp GF),
      "Happly" ∷ rnApplyTok γn A ∗ "Hq" ∷ schedule.schedQueue γs (Ps ++ [pl]) ∗
      "#Hpl" ∷ schedule.savedProp pl Q ∗ "HR" ∷ R ∗
      "#HQR" ∷ □ (Q ∗ R -∗ applyResOn ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ A)) $$ [Happly Hq HR0]
  · iexists [], [n₀], p₀, iprop(True), iprop(applyResOn ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ [])
    simp only [List.cons_append, List.nil_append, List.length_nil, Nat.sub_zero]
    iframe
    iframe Hp0
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
      ⟨%ce, %ceL, Happly, #Hents, #Hentsat, #HC, %Hsnap, Hnc, HG, #Hrac, #Hcl⟩
    -- (D43 M3) `notifyc` and the driver's view, at the apply side (`rnDv`)
    icases Hnc with ⟨%γnc, #Hncb0, Hnrc⟩
    have hρ : ρ.raft = Er.γr.raft := by rw [HEγr, ← Hrd]
    have hpre : γn.pre = ρ.raft.pre := by rw [hρ]; exact Hnm.2.1.symm
    have hnd0 : ρ.raft.raft = γn.node := by rw [hρ, Hnm.1]
    ihave #Hncb : isNotify γnc apv.notifyc' (dvView ρ.raft (rnDv γn ce) (A ++ ce)) $$ []
    · rw [← rnApR_dv γn ρ.raft hpre hnd0 A ce]; iexact Hncb0
    ihave #Hdyn := srvRaftNodeDyn_of_isRaftNode Er γn s $$ Hrn
    icases rnApGive_dv s γn ρ.raft hpre hnd0 A ce $$ [Hdyn HG] with ⟨Hdv, #Hdvr⟩
    · iframe Hdyn HG
    have hdvn : rnDv γn ce = none → ρ.raft.raft.dyn = false ∨ ∀ m, m ∈ ce → m.typ ≠ W32 1 := by
      intro h
      unfold rnDv at h
      by_cases hh : rnHands γn ce
      · rw [ite_eq_left hh] at h; cases h
      unfold rnHands at hh
      cases hd : γn.node.dyn
      · left
        rw [hρ, Hnm.1]
        exact hd
      · right
        rw [hd] at hh
        simp only [Bool.true_and, Bool.not_eq_true] at hh
        intro m hm hty
        unfold ccIn at hh
        have := List.any_eq_false.1 hh m hm
        simp [hty] at this
    have hdvs : ∀ γn', rnDv γn ce = some γn' → uint.Z c₀ ≤ uint.Z ai₀ ∧
        ρ.raft.raft.dyn = true ∧ ρ.raft.raft.dec = srvDec γr.kv.c0 ρ.raft.raft.boot ∧
        ρ.raft.pre = [] ∧ ρ.raft.ai0 = W64 0 := by
      intro γn' h
      unfold rnDv at h
      by_cases hh : rnHands γn ce
      · have hd : γn.node.dyn = true := by
          unfold rnHands at hh; simp only [Bool.and_eq_true] at hh; exact hh.1
        obtain ⟨hc, hp0, ha0⟩ := Hc0a hd
        have hnd : ρ.raft.raft = γn.node := by rw [hρ, Hnm.1]
        refine ⟨hc, by rw [hnd]; exact hd, ?_, by rw [← hpre]; exact hp0, ?_⟩
        · rw [hnd, Hmd hd, HEγr]
        · rw [hρ, HEγr, Hkc0.2]; exact ha0
      · rw [ite_eq_right hh] at h; cases h
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
    imod (schedule.savedProp_alloc (applyResOn ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ (A ++ ce)))
      with ⟨%post, #Hpost⟩
    wp_apply hNJ γs _ _ iprop(R ∗ notifyRcv γnc ∗ dvView ρ.raft (rnDv γn ce) A) Q
        iprop(applyResOn ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ (A ++ ce)) $$ [] as %j #Hj
    · iframe #
      iunfold schedule.jobFnSpec
      iintro !> %ctx %cd !> %Φj ⟨Hrun, ⟨HR', Hnrc, Hdv⟩, HQ, -⟩ HΦj
      ihave Hres := HQR $$ [HQ HR']
      · iframe
      wp_auto
      wp_bind (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyAll"))
        (Val #ep_ptr)) (Val #ap_ptr))
      ihave #Hrac' : rnAdvChan apv.raftAdvancedC'
          (memFloorAtLeast γn.ms γn.γs (uint.Z ai₀ + ((A ++ ce).length : Int))) $$ []
      · rw [show uint.Z ai₀ + ((A ++ ce).length : Int) = ((γn.pre ++ A ++ ce).length : Int) by
          simp only [List.length_append]; push_cast; omega]
        iexact Hrac
      iapply (run_job_bodyOn hAA ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ A ce
        γa hM hRB ap_ptr
        apv.entries' ceL apv.raftAdvancedC' apv.notifyc' γs (rnDv γn ce) γnc hidx hok rfl hdvn hdvs)
        $$ [Hrun Hres Hnrc Hdv]
      · iframe #
        iframe Hrun Hres Hnrc Hdv
        rw [← Hsnap]; iexact snapshotA
      inext
      iintro ⟨Hrun, Hres⟩
      wp_auto
      iapply HΦj
      iframe
    -- `sched.Schedule(f)`, tracked: `Q` the job's `Prev`, its `Post` saved as `post`
    wp_apply hSch sci γs j iprop(R ∗ notifyRcv γnc ∗ dvView ρ.raft (rnDv γn ce) A) Q
        iprop(applyResOn ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ (A ++ ce)) (some (Ps, pl, post))
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
      iprop(applyResOn ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ⟩ (A ++ ce)), iprop(True)
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
    icases Hf with ⟨%id, Hf⟩
    iunfold srvGrantGuard at Hf
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
