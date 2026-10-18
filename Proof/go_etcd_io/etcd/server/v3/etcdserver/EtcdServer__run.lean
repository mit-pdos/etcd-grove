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
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetTerm
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
    (hidx : srvIdxOk C.ai₀ (A ++ ce)) (hok : logShape (A ++ ce))
    (hw : C.γw = ρ.wait) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServer C.s C.γ C.ci TM C.E ρ C.γr ∗ isServerApplyAll C.s C.γr ∗ batchWaitOk ρ C.E (A ++ ce) ∗
        taEntriesAddr apL ↦□ es ∗ taRaftAdvancedCAddr apL ↦□ rac ∗
        rnAdvChan rac (memFloorAtLeast C.ms C.γs (uint.Z C.ai₀ + ((A ++ ce).length : Int))) ∗
        taSnapshotAddr apL ↦□ (null : Loc) ∗ taNotifycAddr apL ↦□ nc ∗ isUnitBag nc ∗
        es ↦*□ ceL ∗ entriesAt ceL ce ∗ batchCommittedIdx C.γr ce ∗ schedule.schedRunning γs ∗
        applyRes C A ∗ srvWTPool C.E.γ ∗ srvRLogLb ρ.raft (A ++ ce) }}
      (App (App (Val (C.s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyAll")) (Val #C.ep))
        (Val #apL))
    {{ RET #(); schedule.schedRunning γs ∗ applyRes C (A ++ ce) }} := by
  iintro %Φ ⟨#Hpkg, #Hsrv, #Hsa, #Hbw, #Hes, #Hrac, #Hracc, #Hsn, #Hnc, #Hncb, #Hesl, #Hents, #Hbc, Hrun, HR,
    #HWc, #Hlbr⟩ HΦ
  iunfold applyRes at HR
  icases HR with ⟨%st, %ai, %at', %a, %t, %cs, %x, Hai, Hat, Hcs, Hss, Hst, Hbe, Happ, Hlr, Hbr,
    Hwr, HKV, Hao, #Hlog, Hkr, %Hpure⟩
  rw [hw]
  obtain ⟨Hloop, Hai0, HJ, Hstep⟩ := Hpure
  iunfold schedule.schedRunning at Hrun
  icases Hrun with ⟨Hrt, Htok⟩
  have habove := srvIdxOk_batch_above C.ai₀ ai A ce hidx Hai0
  have hun : unapplied ai ce = ce := unapplied_all ai ce habove
  have hcong : ∀ m ∈ ce, (uint.Z (ciEff C.γ st.k) < uint.Z m.index ↔ uint.Z C.c₀ < uint.Z m.index) :=
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
  ihave #Hsrv2 := Hsrv
  iunfold isServer at Hsrv2
  icases Hsrv2 with ⟨%Hρr, -⟩
  iunfold kvRun at Hkr
  icases Hkr with ⟨Hka, %Hkc⟩
  ihave #Hkb : iprop(kvBatch C.γr (ciEff C.γ st.k) ai A ce) $$ []
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
  iapply (hAA C.s C.γ C.ci TM C.E ρ C.γr C.b C.ep apL es ceL ce (ai + 1) rac nc st ai at' a t cs x A
      C.ms C.γs hms hb1 Hloop hok') $$ [Hai Hat Hcs Hss Hst Hbe Happ Hlr Hwr Htok Hbr HKV Hao Hka]
  · rw [hun]
    iframe #
    iframe
    iunfold srvGoRes
    iframe
  inext
  iintro ⟨%st', %ai', %at'', %a', %t', %cs', Hai, Hat, Hcs, Hss, Hst, Hbe, Happ, Hlr, Hgr, Hbr, Hao,
      #Hlb, ⟨%x', HKV, %Hx', #Hlog', Hka⟩, %Hpost⟩
  obtain ⟨hloop', hai', hci'⟩ := Hpost
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
  iunfold applyRes
  rw [hw]
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
  intro s γ ci TM E ρ γr Er γn γg γcx γd v b ai₀ at₀ c₀ x₀
  wp_start as Hpre
  iunfold isServerRun at Hpre
  iNamed Hpre
  obtain ⟨HEC, HEγr⟩ := HEr
  wp_apply wp_with_defer as %defer defer
  ihave #Hsrv' := Hsrv
  iunfold isServer at Hsrv'
  icases Hsrv' with ⟨%Hrd, #Hsci, ⟨%fv, #Hfv⟩, #Hat, -⟩
  ihave #Hfv' := Hfv
  iunfold srvFieldsAt at Hfv'
  icases Hfv' with ⟨#Hlgf, %Hslgnn, #Hw, #Hwok, #Hua, #Happl, %HE, %HEo, #Hhook, #Hlv, #Hlok, #Hfc, #Has,
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
  iintro %sn %pm0 %cs0 %sv %Hsv #Hsn #Hpm0 #Hcs0' #Hcsok ⟨%σ0, Htok0, %Hσ0⟩
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
  ihave #Hrh : iprop(isReadyHandler «$r0_ptr» (∃ c : w64, srvCommittedOwn γr c) γr) $$ []
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
      iintro %ci' %Lc !> %Φ' !> ⟨⟨%c, Hown⟩, #HLc, %HciL⟩ HΦ'
      wp_auto
      wp_apply hGCI s γr (some c) $$ [Hown] as %cci ⟨-, Hown, %Hcci⟩
      · iframe #; iunfold srvCommittedOwnOpt; iexact Hown
      iunfold srvCommittedOwnOpt at Hown
      have hc : cci = c := Hcci c rfl
      subst hc
      (try wp_auto)
      wp_if_destruct
      · wp_apply hSCI s γr cci ci' Lc (by word) $$ [Hown] as ⟨Hown, #Hca⟩
        · iframe #; iframe Hown; ipureintro; exact HciL
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
    $$ [Hloop Hrdone Hcomm]
  · rw [HEγr]; iframe #; iframe
  (try wp_auto)
  -- `ep`: the snapshot's conf state (the field `cs`, loaded), index and term (the getters, over
  -- the metadata's `smOpt`, read-only: `ai₀` and `at₀`)
  have hGI' := hGI md DFrac.discard sv.Metadata'
  rw [Hsvi] at hGI'
  have hGT' := hGT md DFrac.discard sv.Metadata'
  rw [Hsvt] at hGT'
  wp_apply hGI' $$ [] as -
  · iframe #
  (try wp_auto)
  wp_apply hGI' $$ [] as -
  · iframe #
  (try wp_auto)
  wp_apply hGT' $$ [] as -
  · iframe #
  (try wp_auto)
  wp_apply hGI' $$ [] as -
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
    #Hlog0, Hkr, Hfs⟩
  obtain ⟨Hloop0, Hc0⟩ := Hst0
  -- (D19i part 1) the start index is the raft log's start (`kvRun`'s, `rnEnvOk`'s)
  iunfold kvRun at Hkr
  icases Hkr with ⟨Hka0, %Hkc0⟩
  ihave Hkr : kvRun γr ai₀ c₀ [] x₀ $$ [Hka0]
  · iunfold kvRun; iframe Hka0; ipureintro; exact Hkc0
  ihave #Henv' := Henv
  iunfold rnEnvOk at Henv'
  icases Henv' with ⟨-, %Hnm, -⟩
  have Hpre0 : uint.Z ai₀ = (γn.pre.length : Int) := by
    rw [← Hkc0.2, ← HEγr]; exact Hnm.2.2
  ihave HR0 : iprop(applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs⟩ []) $$
      [appliedi appliedt confState diskSnapshotIndex memorySnapshotIndex Hfs Hst Hbe Happ Hlr' Hbr Hwr
        HKV Hao Hkr Htok0]
  · iunfold applyRes
    iexists st₀, ai₀, at₀, a₀, t₀, cs, x₀
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
      ipureintro; exact ⟨Hσ0, by word⟩
    iframe Hlog0
    ipureintro
    refine ⟨Hloop0, by simp, Or.inl Hc0.symm, rfl⟩
  -- the loop: the log `A` received, the scheduler's queue ending with the name of `Q`, the last
  -- tracked job's `Post` (the initial `True` before the first job) and the resource `R` the next
  -- job gets from `run` (`applyRes []` before the first job), together `applyRes A`
  ihave HI : iprop(∃ (A : List EntryModel) (Ps : List GName) (pl : GName) (Q R : IProp GF),
      "Happly" ∷ rnApplyTok γn A ∗ "Hq" ∷ schedule.schedQueue γs (Ps ++ [pl]) ∗
      "#Hpl" ∷ schedule.savedProp pl Q ∗ "HR" ∷ R ∗
      "#HQR" ∷ □ (Q ∗ R -∗ applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs⟩ A)) $$ [Happly Hq HR0]
  · iexists [], [n₀], p₀, iprop(True), iprop(applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs⟩ [])
    simp only [List.cons_append, List.nil_append, List.length_nil, Nat.sub_zero]
    iframe
    iframe #
    iintro !> ⟨-, H⟩
    iexact H
  wp_for
  icases HI with ⟨%A, %Ps, %pl, %Q, %R, Happly, Hq, #Hpl, HR, #HQR⟩
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
      ⟨%ce, %ceL, Happly, #Hents, #Hentsat, #HC, %Hsnap, #Hnc, #Hrac, #Hcl⟩
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
    imod (schedule.savedProp_alloc (applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs⟩ (A ++ ce)))
      with ⟨%post, #Hpost⟩
    wp_apply hNJ γs _ _ R Q
        iprop(applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs⟩ (A ++ ce)) $$ [] as %j #Hj
    · iframe #
      iunfold schedule.jobFnSpec
      iintro !> %ctx %cd !> %Φj ⟨Hrun, HR', HQ, -⟩ HΦj
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
      iapply (run_job_body hAA ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs⟩ TM ρ A ce ap_ptr
        apv.entries' ceL apv.raftAdvancedC' apv.notifyc' γs hidx hok rfl) $$ [Hrun Hres]
      · iframe #
        iframe Hrun Hres
        rw [← Hsnap]; iexact snapshotA
      inext
      iintro ⟨Hrun, Hres⟩
      wp_auto
      iapply HΦj
      iframe
    -- `sched.Schedule(f)`, tracked: `Q` the job's `Prev`, its `Post` saved as `post`
    wp_apply hSch sci γs j R Q
        iprop(applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs⟩ (A ++ ce)) (some (Ps, pl, post))
      $$ [HR Hq] as Hq
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
      iprop(applyRes ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs⟩ (A ++ ce)), iprop(True)
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
