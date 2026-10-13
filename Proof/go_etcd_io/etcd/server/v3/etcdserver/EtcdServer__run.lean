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
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.Scheduler__Stop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__getLead
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__setLead
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__isLeader
public import Spec.go_etcd_io.etcd.pkg.v3.notify.Notifier__Notify
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.ServerStats__BecomeLeader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__getCommittedIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__setCommittedIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__start
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__apply
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__stop
public import EtcdDeps.Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import EtcdDeps.Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetTerm
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__revokeExpiredLeases
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Cleanup
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Warn
public import Perennial.Proof.time

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
    (C : ApplyCtx GF) (TM : MetaCI → IProp GF) (ρ : ReqNames) (A ce : List EntryModel)
    (apL : Loc) (es : GoSlice) (ceL : List Loc) (rac nc : GoChan) (γs : schedule.SchedNames)
    (hidx : srvIdxOk C.ai₀ (A ++ ce)) (hok : entriesOk C.c₀ (A ++ ce) C.x₀) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServer C.s C.γ C.ci TM C.E ρ C.γr ∗ isServerApplyAll C.s C.γr ∗ batchWaitOk ρ C.E (A ++ ce) ∗
        taEntriesAddr apL ↦□ es ∗ taRaftAdvancedCAddr apL ↦□ rac ∗
        taSnapshotAddr apL ↦□ (null : Loc) ∗ taNotifycAddr apL ↦□ nc ∗ isUnitBag nc ∗
        es ↦*□ ceL ∗ entriesAt ceL ce ∗ schedule.schedRunning γs ∗ applyRes C A ∗
        txn.storeWTs C.E.γ ce.length }}
      (App (App (Val (C.s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyAll")) (Val #C.ep))
        (Val #apL))
    {{ RET #(); schedule.schedRunning γs ∗ applyRes C (A ++ ce) }} := by
  iintro %Φ ⟨#Hpkg, #Hsrv, #Hsa, #Hbw, #Hes, #Hrac, #Hsn, #Hnc, #Hncb, #Hesl, #Hents, Hrun, HR, HWc⟩ HΦ
  iunfold applyRes at HR
  icases HR with ⟨%st, %ai, %at', %a, %t, %cs, %x, Hai, Hat, Hcs, Hss, Hst, Hbe, Happ, Hlr, Hbr,
    Hwr, HKV, Hao, #Hlog, %Hpure⟩
  obtain ⟨Hloop, Hai0, HJ, Hstep⟩ := Hpure
  iunfold schedule.schedRunning at Hrun
  icases Hrun with ⟨Hrt, Htok⟩
  have habove := srvIdxOk_batch_above C.ai₀ ai A ce hidx Hai0
  have hun : unapplied ai ce = ce := unapplied_all ai ce habove
  have hcong : ∀ m ∈ ce, (uint.Z (ciEff C.γ st.k) < uint.Z m.index ↔ uint.Z C.c₀ < uint.Z m.index) :=
    fun m hm => ciJ_iff _ _ _ HJ m (habove m hm)
  have hok' : entriesOk (ciEff C.γ st.k) (unapplied ai ce) x := by
    rw [hun]
    exact (entriesOk_congr _ _ ce hcong x).2 (entriesOk_append_run C.c₀ A ce C.x₀ x hok Hstep)
  have hb1 : uint.Z ai + 1 < 2 ^ 64 := by
    have h1 := hidx.1
    simp only [List.length_append] at h1
    push_cast at h1
    have : (0 : Int) ≤ ce.length := by omega
    omega
  have hms : ce = [] ∨ (entriesFrom (ai + 1) ce ∧ uint.Z (ai + 1) ≤ uint.Z ai + 1) := by
    by_cases hne : ce = []
    · left; exact hne
    · right
      obtain ⟨h1, h2⟩ := srvIdxOk_batch_from C.ai₀ ai A ce hidx Hai0 hne
      exact ⟨h1, by omega⟩
  ihave #Hbw' : iprop(batchWaitOk ρ C.E ce) $$ []
  · iunfold batchWaitOk at Hbw
    iunfold batchWaitOk
    imodintro
    iintro %m %hm
    iapply Hbw
    ipureintro; exact List.mem_append_right A hm
  iapply (hAA C.s C.γ C.ci TM C.E ρ C.γr C.b C.ep apL es ceL ce (ai + 1) rac nc st ai at' a t cs x
      hms hb1 Hloop hok') $$ [Hai Hat Hcs Hss Hst Hbe Happ Hlr Hwr Htok Hbr HKV Hao HWc]
  · rw [hun]
    iframe #
    iframe
    iunfold srvGoRes
    iframe
  inext
  iintro ⟨%st', %ai', %at'', %a', %t', %cs', Hai, Hat, Hcs, Hss, Hst, Hbe, Happ, Hlr, Hgr, Hbr, Hao,
      #Hlb, ⟨%x', HKV, %Hx', #Hlog'⟩, %Hpost⟩
  obtain ⟨hloop', hai', hci'⟩ := Hpost
  iunfold srvGoRes at Hgr
  icases Hgr with ⟨Hwr, Htok⟩
  iapply HΦ
  iunfold schedule.schedRunning
  iframe Hrt Htok
  iunfold applyRes
  iexists st', ai', at'', a', t', cs', x'
  iframe
  iframe Hlog'
  ipureintro
  rw [hun] at Hx'
  have hlast := srvIdxOk_batch_last C.ai₀ ai A ce hidx Hai0
  refine ⟨hloop', by rw [hai', hlast], ?_, ?_⟩
  · apply ciJ_step _ _ _ ai ai' HJ (by rw [hai']; omega) hci'
  · exact entriesStep_append' C.c₀ A ce C.x₀ x x' Hstep (entriesStep_congr _ _ ce hcong x x' Hx')

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

set_option hygiene false in
/-- `run`'s deferred shutdown (after its loop returns): `stopping` closed under `wgMu`'s write
lock (`GoAttach`'s protocol closed, its "no waiters" taken), the context cancelled, the scheduler
stopped, `GoAttach`'s goroutines waited for, raft stopped, `Cleanup`, `done` closed. -/
local macro "run_shutdown" : tactic => `(tactic| (
  ihave #Htrue : iprop(True) $$ []
  · itrivial
  ihave #Hgok' := Hgok
  iunfold srvGoAttachOk at Hgok'
  icases Hgok' with ⟨%gch, %gc, #Hgstf, #Hgint, #Hgwg, #Hginv, #Hgguard, -, -, -⟩
  wp_apply sync.RWMutex.wp_Lock_guard (srvWgMuAddr s) (wgMuP γg) $$ [] as ⟨Hwl, HP1⟩
  · iframe #
  iunfold wgMuP at HP1
  icases HP1 with ⟨%bo, Hbo, Hso⟩
  imod goAttach_closer_open γg bo _ $$ Hginv Hclose Hbo with ⟨%Hbot, Hclose, Hbo⟩
  subst Hbot
  iunfold stopPart at Hso
  simp only [↓reduceIte]
  (try wp_auto)
  ihave #Hgich : isChan gch γg.ch Unit $$ []
  · iunfold isStopChanInternal at Hgint; icases Hgint with ⟨$, -⟩
  wp_apply_core chan.wp_close (V := Unit) gch γg.ch $$ Hgich
  iintro -
  iapply stop_close_au_internal gch γg.ch γg.chi iprop(True) _ $$ Hgint Hso Htrue
  inext
  iintro #Hdisc
  imod goAttach_shutdown γg $$ Hginv Hclose Hbo Hdisc with ⟨HP1, Hw0⟩
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Unlock_guard (srvWgMuAddr s) (wgMuP γg) $$ [Hwl HP1]
  · iframe #; iframe
  (try wp_auto)
  wp_bind (App (Val #v.cancel) (Val #()))
  iunfold context.cancelSpec at Hcfs
  iapply Hcfs $$ Htrue
  inext
  iintro -
  (try wp_auto)
  wp_apply hStop sci γs (Ps ++ [pl]) $$ [Hstoptok Hq]
  · iframe #; iframe
  (try wp_auto)
  wp_apply wp_goAttach_Wait s γg $$ [Hw0]
  · iframe #; iframe
  (try wp_auto)
  wp_apply hRStop Er γn (srvRAddr s) $$ []
  · iframe #
  (try wp_auto)
  wp_apply hCl s $$ []
  (try wp_auto)
  wp_apply wp_broadcast_chan_close (ty := go.ChannelType go.ChanDir.sendrecv (go.StructType []))
    v.done γd iprop(True) $$ [Hdc]
  · iframe Hdc; iexact Htrue
  iintro -
  (try wp_auto)
  iapply HΦ
  itrivial))

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
    (hSch : schedule.Scheduler.Schedule.spec (GF := GF) (hG := hG))
    (hRev : EtcdServer.revokeExpiredLeases.spec (GF := GF) (hG := hG))
    (hZE : zap.Error.spec (GF := GF) (hG := hG))
    (hW : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hStop : schedule.Scheduler.Stop.spec (GF := GF) (hG := hG))
    (hRStop : raftNode.stop.spec (GF := GF) (hG := hG))
    (hCl : EtcdServer.Cleanup.spec (GF := GF) (hG := hG)) :
    EtcdServer.run.spec (GF := GF) (hG := hG) := by
  intro s γ ci TM E ρ γr Er γn γg γcx γd v b ai₀ at₀ c₀ x₀ N HN
  wp_start as Hpre
  iunfold isServerRun at Hpre
  iNamed Hpre
  obtain ⟨HEC, HEγr⟩ := HEr
  wp_apply wp_with_defer as %defer defer
  ihave #Hsrv' := Hsrv
  iunfold isServer at Hsrv'
  icases Hsrv' with ⟨#Hsci, ⟨%fv, #Hfv⟩, #Hat⟩
  ihave #Hfv' := Hfv
  iunfold srvFieldsAt at Hfv'
  icases Hfv' with ⟨#Hlgf, %Hslgnn, #Hw, #Hwok, #Hua, #Happl, %HE, #Hhook, #Hlv, #Hlok, #Hfc, #Has,
    #Hcl, #Hq, #Hlgmu, #Hmid, #Hlead, #Het, #Htm, #Hnot, #Halm⟩
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
  · iframe #; iframe Hlr; ipureintro; exact Hslgnn
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
  iintro %sn %md %cs %pi %pt %Hsnn #Hmd #Hcs #Hpi #Hpiv #Hpt #Hptv
  obtain ⟨Hsn0, Hmd0, Hcs0⟩ := Hsnn
  (try wp_auto)
  -- the FIFO scheduler: its stop token, its queue `[n₀, p₀]` (`p₀` saving `True`)
  wp_apply hFifo fv.lg $$ [] as %sc ⟨%γs, %n₀, %p₀, #Hfifo, Hstoptok, Hq, #Hp0⟩
  · iframe #; ipureintro; exact Hlg0
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
  ihave #Hrh : iprop(isReadyHandler «$r0_ptr» (∃ c : w64, srvCommittedOwn γr c)) $$ []
  · iunfold isReadyHandler
    iexists _, _, _, _
    iframe getLead updateLead updateLeadership updateCommittedIndex
    isplitr
    · -- `getLead`
      iintro !> %Φ' !> - HΦ'
      wp_auto
      wp_apply hGL s $$ [] as %ld -
      · iframe #
      (try wp_auto)
      iapply HΦ'
      itrivial
    isplitr
    · -- `updateLead`
      iintro %ld !> %Φ' !> - HΦ'
      wp_auto
      wp_apply hSL s ld $$ []
      · iframe #
      (try wp_auto)
      iapply HΦ'
      itrivial
    isplitr
    · -- `updateLeadership`
      iintro %nl !> %Φ' !> - HΦ'
      wp_auto
      wp_apply hIL s fv.memberID $$ [] as %isl -
      · iframe #
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
      cases isl
      · -- not the leader: `Demote`, `Pause`
        simp only [Bool.not_false]
        (try wp_auto)
        rw [Hli]
        (try wp_auto)
        wp_apply HDemote
        (try wp_auto)
        icases Hcpok' with (%Hcpn | ⟨%cpi, %Hcpi, #HPause, #HResume⟩)
        · rw [Hcpn]
          ul_tail
        · rw [Hcpi]
          (try wp_auto)
          wp_apply HPause
          ul_tail
      · -- the leader: the election time (if new), `Resume`
        simp only [Bool.not_true]
        (try wp_auto)
        cases nl
        · (try wp_auto)
          icases Hcpok' with (%Hcpn | ⟨%cpi, %Hcpi, #HPause, #HResume⟩)
          · rw [Hcpn]
            ul_stats
          · rw [Hcpi]
            (try wp_auto)
            wp_apply HResume
            ul_stats
        · (try wp_auto)
          wp_apply time.wp_Now as %tn -
          (try wp_auto)
          wp_apply sync.RWMutex.wp_Lock_guard (srvLeadTimeMuAddr s) (leadTimeP s) $$ [] as ⟨Hwl, HP⟩
          · iframe #
          iunfold leadTimeP at HP
          icases HP with ⟨%t0, Hlt⟩
          (try wp_auto)
          wp_apply sync.RWMutex.wp_Unlock_guard (srvLeadTimeMuAddr s) (leadTimeP s) $$ [Hwl Hlt]
          · iframe #; iframe Hwl; iunfold leadTimeP; iexists _; iexact Hlt
          (try wp_auto)
          icases Hcpok' with (%Hcpn | ⟨%cpi, %Hcpi, #HPause, #HResume⟩)
          · rw [Hcpn]
            (try wp_auto)
            wp_apply hN v.leaderChanged $$ []
            · iframe #
            ul_stats
          · rw [Hcpi]
            (try wp_auto)
            wp_apply HResume
            (try wp_auto)
            wp_apply hN v.leaderChanged $$ []
            · iframe #
            ul_stats
    · -- `updateCommittedIndex`: the writer's half of the committed index
      iintro %ci' !> %Φ' !> ⟨%c, Hown⟩ HΦ'
      wp_auto
      wp_apply hGCI s γr (some c) $$ [Hown] as %cci ⟨-, Hown, %Hcci⟩
      · iframe #; iunfold srvCommittedOwnOpt; iexact Hown
      iunfold srvCommittedOwnOpt at Hown
      have hc : cci = c := Hcci c rfl
      subst hc
      (try wp_auto)
      wp_if_destruct
      · wp_apply hSCI s γr cci ci' (by word) $$ [Hown] as ⟨Hown, -⟩
        · iframe #; iexact Hown
        (try wp_auto)
        iapply HΦ'
        iexists ci'; iexact Hown
      · (try wp_auto)
        iapply HΦ'
        iexists cci; iexact Hown
  -- `s.r.start(rh)`: the raft loop, owning the committed index's writer half
  wp_apply hRS Er γn (srvRAddr s) «$r0_ptr» [] (∃ c : w64, srvCommittedOwn γr c)
    $$ [Hloop Hrdone Hcomm]
  · iframe #; iframe
  (try wp_auto)
  -- `ep`: the snapshot's conf state, index and term
  ihave #HmdI : iprop(⌜md = null ∧ ai₀ = W64 0⌝ ∨ ∃ pi : Loc, ⌜md ≠ null⌝ ∗
      structFieldRef go_etcd_io.raft.v3.raftpb.SnapshotMetadata go!"Index" md ↦□ pi ∗ optU64 pi ai₀) $$ []
  · iright; iexists pi; iframe #; ipureintro; exact Hmd0
  ihave #HmdT : iprop(⌜md = null ∧ at₀ = W64 0⌝ ∨ ∃ pt : Loc, ⌜md ≠ null⌝ ∗
      structFieldRef go_etcd_io.raft.v3.raftpb.SnapshotMetadata go!"Term" md ↦□ pt ∗ optU64 pt at₀) $$ []
  · iright; iexists pt; iframe #; ipureintro; exact Hmd0
  wp_apply hGI md ai₀ $$ []
  · iframe #
  (try wp_auto)
  wp_apply hGI md ai₀ $$ []
  · iframe #
  (try wp_auto)
  wp_apply hGT md at₀ $$ []
  · iframe #
  (try wp_auto)
  wp_apply hGI md ai₀ $$ []
  · iframe #
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
    #Hlog0, Hfs⟩
  obtain ⟨Hloop0, Hc0⟩ := Hst0
  ihave HR0 : iprop(applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀⟩ []) $$
      [appliedi appliedt confState diskSnapshotIndex memorySnapshotIndex Hfs Hst Hbe Happ Hlr' Hbr Hwr
        HKV Hao]
  · iunfold applyRes
    iexists st₀, ai₀, at₀, a₀, t₀, cs, x₀
    iframe
    isplitl
    · iunfold srvSnapState; iexists ai₀, ai₀, f₀; iframe
    iframe Hlog0
    ipureintro
    refine ⟨Hloop0, by simp, Or.inl Hc0.symm, rfl⟩
  -- the loop: the log `A` received, the scheduler's queue ending with the name of `Q`, the last
  -- tracked job's `Post` (the initial `True` before the first job) and the resource `R` the next
  -- job gets from `run` (`applyRes []` before the first job), together `applyRes A`
  ihave HI : iprop(∃ (A : List EntryModel) (Ps : List GName) (pl : GName) (Q R : IProp GF),
      "Happly" ∷ rnApplyTok γn A ∗ "Hq" ∷ schedule.schedQueue γs (Ps ++ [pl]) ∗
      "#Hpl" ∷ schedule.savedProp pl Q ∗ "HR" ∷ R ∗
      "#HQR" ∷ □ (Q ∗ R -∗ applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀⟩ A) ∗
      "HWB" ∷ txn.storeWTs E.γ (N - A.length)) $$ [Happly Hq HR0 HWB]
  · iexists [], [n₀], p₀, iprop(True), iprop(applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀⟩ [])
    simp only [List.cons_append, List.nil_append, List.length_nil, Nat.sub_zero]
    iframe
    iframe #
    iintro !> ⟨-, H⟩
    iexact H
  wp_for
  icases HI with ⟨%A, %Ps, %pl, %Q, %R, Happly, Hq, #Hpl, HR, #HQR, HWB⟩
  wp_apply (lc := 2) hRA Er γn (srvRAddr s) $$ [] as %apc #Hapc
  · iframe #
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
      ⟨%ce, %ceL, Happly, #Hents, #Hentsat, #HC, %Hsnap, #Hnc, #Hrac⟩
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
    icases HC'' with ⟨%Hcp, #Hbw⟩
    obtain ⟨hidx, hok⟩ := Hcp
    imod (schedule.savedProp_alloc (applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀⟩ (A ++ ce)))
      with ⟨%post, #Hpost⟩
    wp_apply hNJ γs _ _ iprop(R ∗ txn.storeWTs E.γ ce.length) Q
        iprop(applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀⟩ (A ++ ce)) $$ [] as %j #Hj
    · iframe #
      iunfold schedule.jobFnSpec
      iintro !> %ctx %cd !> %Φj ⟨Hrun, ⟨HR', HWBc⟩, HQ, -⟩ HΦj
      ihave Hres := HQR $$ [HQ HR']
      · iframe
      wp_auto
      wp_bind (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyAll"))
        (Val #ep_ptr)) (Val #ap_ptr))
      iapply (run_job_body hAA ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀⟩ TM ρ A ce ap_ptr
        apv.entries' ceL apv.raftAdvancedC' apv.notifyc' γs hidx hok) $$ [Hrun Hres HWBc]
      · iframe #
        iframe Hrun Hres HWBc
        rw [← Hsnap]; iexact snapshotA
      inext
      iintro ⟨Hrun, Hres⟩
      wp_auto
      iapply HΦj
      iframe
    -- `sched.Schedule(f)`, tracked: `Q` the job's `Prev`, its `Post` saved as `post`
    have hle : A.length + ce.length ≤ N := by
      have h1 := hidx.1
      simp only [List.length_append] at h1
      push_cast at h1
      have : (0 : Int) ≤ uint.Z ai₀ := by word
      omega
    rw [show N - A.length = ce.length + (N - (A ++ ce).length) by
      simp only [List.length_append]; omega] at *
    icases (txn.storeWTs_add E.γ ce.length (N - (A ++ ce).length)).1 $$ HWB with ⟨HWBc, HWB⟩
    wp_apply hSch sci γs j iprop(R ∗ txn.storeWTs E.γ ce.length) Q
        iprop(applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀⟩ (A ++ ce)) (some (Ps, pl, post))
      $$ [HR HWBc Hq] as Hq
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
      iprop(applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀⟩ (A ++ ce)), iprop(True)
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    iframe
    iframe #
    iunfold named
    iintro !> ⟨H, -⟩
    iexact H
  -- `leases := <-expiredLeaseC`: revoked (names-only)
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
    iintro %ls -
    wp_auto
    wp_apply hRev s ls $$ []
    (try wp_auto)
    wp_for_post
    iframe
    iexists A, Ps, pl, Q, R
    iframe
    iframe #
  -- `err := <-s.errorc`: warn, return
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
    iintro %err -
    wp_auto
    wp_apply hZE err as %ef -
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply hW fv.lg _ _ $$ []
    · iframe #; ipureintro; exact Hlg0
    (try wp_auto)
    wp_apply hW fv.lg _ _ $$ []
    · iframe #; ipureintro; exact Hlg0
    (try wp_auto)
    wp_for_post
    run_shutdown
  -- `<-s.stop`: return
  iapply BigAndL.bigAndL_cons.2
  isplit
  · iunfold isUnitBag at Hscb
    icases Hscb with ⟨%γst, #Hstb⟩
    simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, v.stop, γst
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hstb
    iapply bag_recv_au γst v.stop _ _ $$ [$Hlc1 $Hlc2] Hstb
    inext
    iintro %u -
    wp_auto
    wp_for_post
    run_shutdown
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial
