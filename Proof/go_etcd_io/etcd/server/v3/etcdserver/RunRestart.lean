/-
**`run`'s restart branch** (R2d'a A10 item 4, 2026-11-06; DRAFT: nothing here is frozen, and no
closed theorem imports this file; `notes/restart-plan.md`, "R2d'a A10 item 4"). Lean-first (no Rocq
counterpart).

`run.wp_proofG` over the restart's conjuncts (A9's `srvRunRestartR`, `σ.b = 0`): the apply thread's
loop resources in restart form (`applyResR` at the restart point `⟨0, A₀⟩`, from `applyResR_start`),
the batch jobs over `applyAll.specBatchR` (`run_job_bodyR`, with `Hwpend`'s window token borrowed by
`winNoMergedSendR`), the stop inside the window over `StopR.lean`'s pieces and past it the frozen path.
The snapshot jobs over `applyAll.specSnapMR` (`run_job_snapCR`, `RunSnapR.lean`), inside the window
or past it. One `sorry` left, a pure fact: inside the window, the snapshot above the backend's log
(`|A₀| < |A'|`, A8's `rnWinInstallAbove`), which the raft loop holds at the snapshot's `Ready` but
the payload `rnApSnap` does not carry to the apply thread (task 4's report).
* `isServerRunCR`: `isServerRunC` with `%HEr`, `Hsnap` and `Hstart` replaced by `srvRunRestartR`
  (A9's texts; the hub edit waits for the go, Q20);
* `run.specR`: `run.spec` over `isServerRunCR`;
* `run.wp_proofR`: its proof.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__run
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RunR
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StartR
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StopR
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ViewR
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RunSnapR

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **What `run` needs at a restart** (DRAFT; `isServerRunC` with A9's `srvRunRestartR` in place of
`%HEr`, `Hsnap` and `Hstart`). -/
def isServerRunCR (C : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (γg : GoNames) (γcx : context.ContextNames) (γd : ChanNames) (v : RunFields)
    (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV)
    (SP : IProp GF := iprop(False)) (DQ : IProp GF := iprop(True)) : IProp GF :=
  iprop("#Hsrv" ∷ isServerC C s γ ci TM E ρ γr ∗
    "#Hlnil" ∷ acLessor C s ∗
    "#Hsa" ∷ isServerApplyAll s γr ∗
    -- (J8b, 2026-11-01) the server's member id is the raft node's (`isServerBuilt`'s)
    "#Hmid" ∷ srvMemberIDAddr s ↦□ γn.id ∗
    -- (J8b, 2026-11-01) the meta reads of the backends a snapshot opens (`bootOk`'s `#HmetaSnap`)
    "#HmetaSnap" ∷ srvMetaSnap γ ∗
    "#Hrn" ∷ isRaftNode Er γn (srvRAddr s) ∗
    -- (R2d'a A9, DRAFT) `%HEr`, `Hsnap` and `Hstart` at a restart (`σ.b = 0`): the backend's ghost
    -- log `A₀ = γn.a0`, the storage's snapshot's conf state at it, the apply thread's ghost rows at it
    "HRr" ∷ srvRunRestartR C s γ ci b E ρ γr Er γn ai₀ at₀ c₀ x₀ ρ.wait ∗
    -- (R2d'a A7, A10 item 5, 2026-11-06; DRAFT, approved by 82) no merged snapshot sent at a new
    -- raft term while the replay window is pending (`srvWinPend`; a restart-only premise, R2s's
    -- target; free at a first start, `srvWinPend_first`)
    "Hwpend" ∷ srvWinPend s γr γn ∗
    -- (2026-10-30, the repair) the apply side's half of the node's running token
    "Hrunh" ∷ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half) ∗
    -- (2026-10-31) the WAL's open token: the apply side's half (its disk snapshot's `SaveSnap`, which
    -- `run` gives the raft loop with `raftNode.stop`) and the loop's (`raftNode.start`'s); the disk
    -- cooperating (`storage.diskOk`, `NewServer`'s premise)
    "Hwth" ∷ rnWalTokA γn (srvRAddr s) (1 : Qp).half ∗ "Hwtl" ∷ rnWalTokL γn (srvRAddr s) ∗
    "%Hdisk" ∷ ⌜storage.diskOk⌝ ∗
    -- (2026-11-02, the lease-grant plan's D2) in a cluster that grants leases, the open
    -- cases (`srvGrantOpen`, `NewServer`'s precondition); (2026-11-04, the lease-expiry plan's
    -- Part C) as the lease subsystem's sealed premise at some mode (`lease.runCfg`)
    "%Hslg" ∷ ⌜∃ m : lease.Mode, lease.runCfg (GF := GF) γr.kv.lm m⌝ ∗
    -- (2026-10-31, #11) the KV the snapshot commits (`start`'s `srvReadBuilt`)
    "#Hkvf" ∷ (∃ kv : GoInterface, srvKVAddr s ↦□ kv ∗ txn.isKV kv E.s E.γ) ∗
    "#Hrf" ∷ srvRunFieldsAt s γr γg γcx v SP ∗
    -- (revoke-open, 2026-11-06) the revocation's bundle (`run`'s expiry arm, revocable mode)
    "#Hrvk" ∷ srvRevokeCtx s E ρ γr γg ∗
    "Hloop" ∷ rnLoopTok γn [] ∗ "Hsend" ∷ Er.S ∗ "Happly" ∷ rnApplyTok γn [] ∗ "Hrdone" ∷ rnDoneTok γn (srvRAddr s) ∗
    "Hcomm" ∷ (∃ c : w64, srvCommittedOwn γr c) ∗
    "Hdc" ∷ ownBroadcastChan v.done γd DQ .Pending ∗
    "Hclose" ∷ token γg.close ∗
    "Hlr" ∷ srvLgReader s ∗
    -- (2026-10-19, D21 M3) with its counter, the apply thread's tokens taken through `ai₀`
    -- (H2, 2026-11-05) and its register at `GoAttach`'s receipts' name (`start` set it)
    "#HWB" ∷ (∃ γp : WTNames, srvWTPool E γp ∗ srvWTAt γp.cnt ai₀ ∗
      dghostVar γp.reg DFrac.discard (some γg.run)) ∗
    -- (2026-10-26, D22 J1a) what the snapshot path takes of the construction (`SnapRO.lean`): its
    -- persistent bundle; (D22 J1b, 2026-10-31) the counter's authority and the stocks in `applyStart`
    "#Hsnapb" ∷ (∃ γt : GName, srvSnapRO s ci E γr γt) ∗
    -- (J8a-3, 2026-11-01) the two configuration fields `start` writes, read-only from then on:
    -- with `srvSnapRO`'s rebuild, the whole configuration read-only (`specSnap`'s `srvCfgAddr s ↦□`)
    "#Hsncfg" ∷ (∃ sc scu : w64, srvCfgFieldAddr s go!"SnapshotCount" ↦□ sc ∗
      srvCfgFieldAddr s go!"SnapshotCatchUpEntries" ↦□ scu) ∗
    -- (R2c-4) the stop's slot (`srvStop.slot`), from `start`'s construction premise, for the
    -- deferred shutdown
    "Hskeep" ∷ srvStop.slot s E γn Er)

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`run` at a restart** (DRAFT): `run.spec` over `isServerRunCR`. -/
abbrev EtcdServer.run.specR : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (C : AuthC) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames) (γg : GoNames)
    (γcx : context.ContextNames) (γd : ChanNames) (v : RunFields) (b : GoInterface)
    (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (dd : GoString) (c : GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      ⌜E.authMode = C.mode ∧ acReceiptOk (GF := GF) C⌝ ∗
      isServerRunCR C s γ ci TM E ρ γr Er γn γg γcx γd v b ai₀ at₀ c₀ x₀ (srvStopReq s E ρ dd)
        (srvDoneInv ρ.rd.raft.raft ρ γn.id dd c) ∗ threadTok }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"run")) (Val #()))
  {{ RET #(); threadTok }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]


/-- `run_job_bodyR`'s running half, as `srvRunH` (`run_job_body_match`'s). -/
theorem run_job_bodyR_match (γs : ServerRaftNames) (dv : Option Loc) :
    EtcdServer.applyAll.specBatchR.match_1 (fun _ => IProp GF) dv (fun _ => iprop(True))
      (fun n => letI := srvStor (GF := GF) γs.raft; nodeRunning (GF := GF) n γs.raft.cl srvClusterN (1 : Qp).half) =
      srvRunH (GF := GF) γs dv := by
  cases dv <;> rfl

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
/-- **`run` at a restart** (R2d'a A10 item 4, DRAFT): `run.wp_proofG` over `isServerRunCR`. Its one
`sorry`: the snapshot arm's in-window bound `|A₀| < |A'|` (`hwin`; see the header). -/
theorem EtcdServer.run.wp_proofR
    (hSStop : schedule.Scheduler.Stop.spec (GF := GF) (hG := hG))
    (hRStop : raftNode.stop.spec (GF := GF) (hG := hG))
    (hCl : stopCleanupImage.spec (GF := GF) (hG := hG))
    (hClR : stopCleanupImageR.spec (GF := GF) (hG := hG))
    (hAB : EtcdServer.applyAll.specBatchR (GF := GF) (hG := hG))
    (hAS : EtcdServer.applyAll.specSnapMR (GF := GF) (hG := hG))
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
    EtcdServer.run.specR (GF := GF) (hG := hG) := by
  intro s γ ci TM C E ρ γr Er γn γg γcx γd v b ai₀ at₀ c₀ x₀ dd c
  wp_start as ⟨%hP, Hpre, Htok⟩
  obtain ⟨hM, hRB⟩ := hP
  iunfold isServerRunCR at Hpre
  iNamed Hpre
  -- (R2d'a A9) the restart's conjuncts: the backend's ghost log `A₀ = γn.a0`
  iunfold srvRunRestartR at HRr
  icases HRr with ⟨%A₀, %HEr, Hsnap, Hstart⟩
  obtain ⟨HEC, HEγr, Hc0a, Ha0, Hty0, Hbnd0⟩ := HEr
  -- (A10 item 5) the raft node's `MsgSnap` bag at `γn` (`isRaftNode`'s), for the merged send's case
  -- `rt ≤ t0`; `Hwpend`'s token and wand
  ihave #Hbagn : srvSnapBagN s γn $$ []
  · iunfold srvSnapBagN
    iframe Hmid
    ihave #Hrn0 := Hrn
    iunfold isRaftNode at Hrn0
    iNamed Hrn0
    iexists _
    iframe Hmsc Hmsci
  iunfold srvWinPend at Hwpend
  icases Hwpend with ⟨%γwp, Hwp, #Hwpw⟩
  icases HWB with ⟨%γp, #HWB, #HWA0, #HWreg⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsrv' := (isServerM_C C s γ ci TM E ρ γr).2 $$ Hsrv
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
  iunfold rnSnapOnceR at Hsnap
  iapply Hsnap
  inext
  iintro %sn %pm0 %cs0 %sv %Hsv #Hsn #Hpm0 #Hcs0' #Hcsok #HcsA0 Hnone #Hmsinv
  -- (2026-10-31, #11) the snapshot's disk side, from the construction's bundle and the node
  icases Hsnapb with ⟨%γt, #Hsro⟩
  ihave #Hsd : srvSnapDisk s γr $$ []
  · iapply srvSnapDisk_of_RO s ci E γr γt Er γn
    iframe Hsro Hrn
  -- (2026-10-30, the repair) the storage's stored snapshot index at least `0`
  imod Hnone with #Hslb0
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
  wp_apply hFifo fv.lg iprop(True) $$ [] as %sc ⟨%γs, %n₀, %p₀, #Hfifo, Hstoptok, Hq, #Hp0, #Hpay⟩
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
  -- (R2d'a A10 item 3) the restart data, read from the loop's token before the start (the stop's
  -- bound, `rnRestartOk_commit`)
  ihave ⟨Hloop, #Hrok⟩ := rnLoopTok_restartOk γn [] $$ Hloop
  wp_apply hRS Er γn (srvRAddr s) «$r0_ptr» [] (∃ c : w64, srvCommittedOwn γr c) Hdisk.2.2.1 Hdisk.2.2.2.1
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
  -- (R2d'a A10 item 4) the apply thread's resources at the restart's start (`applyResR_start`,
  -- Go's handed log `P = []`, the ghost log `A₀`)
  ihave ⟨Hstart, %Hkc0, #HlbA0⟩ : iprop(srvRestartAtR C s γ ci b E γr ai₀ c₀ x₀ ρ.wait A₀ ai₀ ∗
      ⌜γr.kv.c0 = c₀ ∧ γr.raft.ai0 = ai₀⌝ ∗ srvRLogLb γr.raft A₀) $$ [Hstart]
  · iunfold srvRestartAtR at Hstart
    icases Hstart with ⟨%st₀, %a₀, %t₀, %f₀, %g₀, Hst, %Hst0, Hbe, Happ, Hlr', Hbr, Hwr, HKV, Hao,
      Hal, Hkr, HRS, HAR, Hfs, HtokR, Hso⟩
    ihave Hkr : iprop(kvAppliedM C.isOn γr.raft γr.kv srvAuthSt0 A₀ x₀ srvAuthSt0 ∗
        ⌜γr.kv.c0 = c₀ ∧ γr.raft.ai0 = ai₀⌝) $$ [Hkr]
    · rw [← kvRunM_split]; iexact Hkr
    icases Hkr with ⟨Hka0, %Hkc0⟩
    ihave Hkr : kvRunM C.isOn γr ai₀ c₀ A₀ x₀ srvAuthSt0 $$ [Hka0]
    · rw [kvRunM_split]; iframe Hka0; ipureintro; exact Hkc0
    icases kvRunM_lbR _ _ _ _ _ _ _ $$ Hkr with ⟨#HlbA0, Hkr⟩
    isplitl [Hst Hbe Happ Hlr' Hbr Hwr HKV Hao Hal Hkr HRS HAR Hfs HtokR Hso]
    · iunfold srvRestartAtR
      iexists st₀, a₀, t₀, f₀, g₀
      iframe Hst Hbe Happ Hlr' Hbr Hwr HKV Hao Hal Hkr HRS HAR Hfs HtokR Hso
      ipureintro; exact Hst0
    isplitr
    · ipureintro; exact Hkc0
    iexact HlbA0
  ihave #Henv' := Henv
  iunfold rnEnvOk at Henv'
  icases Henv' with ⟨-, %Hnm, %Hmd, -⟩
  have Hpre0 : uint.Z ai₀ = (γn.pre.length : Int) := by
    rw [← Hkc0.2, ← HEγr]; exact Hnm.2.2
  have hρr0 : ρ.raft = γr.raft := by rw [← Hrd]
  ihave HR0 : iprop(applyResR C ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩ ⟨0, A₀⟩ []) $$
      [appliedi appliedt confState diskSnapshotIndex memorySnapshotIndex Hstart Hwth]
  · iapply (applyResR_start C ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩ TM [] A₀ ai₀ at₀ cs (List.nil_prefix)
      (by simp) (Or.inl rfl) Hc0a.1 Hty0 Hbnd0 hρr0)
    iframe Hsrv appliedi appliedt confState Hcsok diskSnapshotIndex memorySnapshotIndex Hkvf Hwth Hstart
    isplitr
    · rw [hρr0]; iexact HcsA0
    isplitr
    · rw [← Hmsγ]; iexact Hms
    isplitr
    · iExactEq Hslb0; rfl
    iexists uint.nat ai₀
    rw [← srvWTAt_taken]
    iexact HWA0
  -- the loop: the log `A` received, the scheduler's queue ending with the name of `Q`, the last
  -- tracked job's `Post` (the initial `True` before the first job) and the resource `R` the next
  -- job gets from `run` (`applyRes []` before the first job), together `applyRes A`
  ihave HI : iprop(∃ (A : List EntryModel) (Ps : List GName) (pl : GName) (Q R : IProp GF),
      "Happly" ∷ rnApplyTok γn A ∗ "Hq" ∷ schedule.schedQueue γs (Ps ++ [pl]) ∗
      "#Hpl" ∷ schedule.savedProp pl Q ∗ "HR" ∷ R ∗
      "#HQR" ∷ □ (Q ∗ R -∗ applyResR C ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩ ⟨0, A₀⟩ A ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half) ∗ token γwp) ∗
      -- (R2d'a A10 item 3) Go's handed log committed, for the stop inside the window
      "#HlbA" ∷ srvRLogLb ρ.raft A) $$ [Happly Hq HR0 Hrunh Hwp]
  · iexists [], [n₀], p₀, iprop(True), iprop(applyResR C ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩ ⟨0, A₀⟩ [] ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half) ∗ token γwp)
    simp only [List.cons_append, List.nil_append]
    iframe
    iframe Hp0
    isplitl [HR0 Hrunh Hwp]
    · iunfold named
      isplitl [HR0]
      · iexact HR0
      isplitl [Hrunh]
      · iExactEq Hrunh; rfl
      iexact Hwp
    isplitr
    · iintro !> ⟨-, H⟩
      iexact H
    rw [hρr0]
    iapply srvRLogLb_mono γr.raft [] A₀ List.nil_prefix $$ HlbA0
  wp_for
  icases HI with ⟨%A, %Ps, %pl, %Q, %R, Happly, Hq, #Hpl, HR, #HQR, #HlbA⟩
  wp_apply (lc := 2) hRA Er γn (srvRAddr s) $$ [] as %apc #Hapc
  · iframe Hrn
  (try wp_auto)
  ihave #Hapc' := Hapc
  iunfold isRNApplyc at Hapc'
  ihave #Hapch : isChan apc γn.ap.chanName toApply $$ []
  · unfold isSspsc; icases Hapc' with ⟨$, -⟩
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
    iapply sspsc_rcv_au γn.ap apc _ _ rcv _ $$ Hapc' [$Hlc1 $Hlc2] Hcons
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
    · -- (R2d'a task 4, DRAFT) the snapshot arm: `run_job_snapCR` over `applyAll.specSnapMR`, inside
      -- the window or past it, `Hwpend`'s token framed; scheduled as the frozen arm's
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
      -- the snapshot above the ghost log: past the window Go's `|A| < |A'|`; inside it A8's bound
      -- (`rnWinInstallAbove`), which the raft loop holds at the snapshot's `Ready` but which the
      -- payload (`rnApSnap`) does not carry to the apply thread: the one gap left (task 4's report)
      have hwin : (ghostOf ⟨0, A₀⟩ A).length < A'.length := by
        by_cases hw : A₀.length ≤ A.length
        · rw [ghostOf_past ⟨0, A₀⟩ A hw]; exact hlt
        · have hab : A₀.length < A'.length := sorry
          have := ghostOf_length ⟨0, A₀⟩ A
          simp only at this
          omega
      ihave #HC' : iprop(srvCM C.isOn ρ E ai₀ c₀ x₀ A') $$ []
      · rw [← HEC]; iexact HC
      (try wp_auto)
      wp_func_lits
      (try wp_auto)
      ipersist ap
      ihave #Hapf := ap
      iStructNamedSuffix Hapf "A"
      ihave #HC'' := HC'
      iunfold srvCM at HC''
      icases HC'' with ⟨-, -, #Hlbr⟩
      imod (schedule.savedProp_alloc iprop(applyResR C ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩ ⟨0, A₀⟩ A' ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half) ∗ token γwp))
        with ⟨%post, #Hpost⟩
      wp_apply hNJ γs _ _ iprop(R ∗ notifyRcvN γnc 0) Q
          iprop(applyResR C ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩ ⟨0, A₀⟩ A' ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half) ∗ token γwp) $$ [] as %j #Hj
      · iframe #
        iunfold schedule.jobFnSpec
        iintro !> %ctx %cd !> %Φj ⟨Hrun, ⟨HR', Hnrc⟩, HQ, -, -⟩ HΦj
        ihave ⟨Hres, Hhalf, Hwp⟩ := HQR $$ [HQ HR']
        · iframe
        wp_auto
        wp_bind (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyAll"))
          (Val #ep_ptr)) (Val #ap_ptr))
        iapply (run_job_snapCR hAS ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩ ⟨0, A₀⟩ A A' ap_ptr apv.entries' apv.snapshot' sv
          apv.raftAdvancedC' apv.notifyc' γs γnc γn apv.raftTerm' C hM ha0 Hc0a.1 hp0 hgn hρC
          (by rw [← hρC, hρ]; exact Hnm.2.1) rfl rfl hwin hlenA h61 hboot rfl) $$ [Hrun Hres Hnrc]
        · iframe #
          iframe Hrun Hres Hnrc
        inext
        iintro ⟨Hrun, Hres⟩
        wp_auto
        iapply HΦj
        iframe
      wp_apply hSch sci γs j iprop(R ∗ notifyRcvN γnc 0) Q
          iprop(applyResR C ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩ ⟨0, A₀⟩ A' ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half) ∗ token γwp) (some (Ps, pl, post))
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
      iexists A', Ps ++ [pl], post, iprop(applyResR C ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩ ⟨0, A₀⟩ A' ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half) ∗ token γwp), iprop(True)
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
    -- (R2d'a A10 item 4) over the ghost log (`rnApR_dvG`/`rnApGive_dvG`, no `γn.a0 = []`)
    have hp0' : γn.pre = [] := Hc0a.2.1
    have hrp : ρ.raft.pre = [] := by rw [← hpre]; exact hp0'
    ihave #Hncb : isNotify γnc apv.notifyc' (dvView ρ.raft (rnDv γn ce) (ghostOf ⟨0, A₀⟩ (A ++ ce))) $$ []
    · have h := rnApR_dvG (GF := GF) γn ρ.raft 0 hrp hnd0 A ce
      simp only [hp0', Ha0, List.nil_append] at h
      rw [← h]; iexact Hncb0
    ihave #Hdyn := srvRaftNodeCC_of_isRaftNode Er γn s $$ Hrn
    have hGv := rnApGive_dvG (GF := GF) s γn ρ.raft 0 hrp hnd0 A ce
    simp only [hp0', Ha0, List.nil_append] at hGv
    icases hGv $$ [Hdyn HG] with ⟨Hdv, #Hdvr⟩
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
    ihave #HC' : iprop(srvCM C.isOn ρ E ai₀ c₀ x₀ (A ++ ce)) $$ []
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
    imod (schedule.savedProp_alloc iprop(applyResR C ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩ ⟨0, A₀⟩ (A ++ ce) ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half) ∗ token γwp))
      with ⟨%post, #Hpost⟩
    wp_apply hNJ γs _ _ iprop(R ∗ notifyRcv γnc ∗ dvView ρ.raft (rnDv γn ce) (ghostOf ⟨0, A₀⟩ A)) Q
        iprop(applyResR C ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩ ⟨0, A₀⟩ (A ++ ce) ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half) ∗ token γwp) $$ [] as %j #Hj
    · iframe #
      iunfold schedule.jobFnSpec
      iintro !> %ctx %cd !> %Φj ⟨Hrun, ⟨HR', Hnrc, Hdv⟩, HQ, -, -⟩ HΦj
      ihave ⟨Hres, Hhalf, Hwp⟩ := HQR $$ [HQ HR']
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
            srvFrozenTerms γn.γs (uint.nat ai₀ + 1) (A ++ ce) ∗
            rnWalHanded γn (uint.nat ai₀ + (A ++ ce).length))) $$ []
      · rw [hnd0, show uint.nat ai₀ + (A ++ ce).length = (γn.pre ++ A ++ ce).length by
            simp [hp0, ha0],
          show uint.nat ai₀ + A.length + 1 = (γn.pre ++ A).length + 1 by simp [hp0, ha0],
          show uint.nat ai₀ + 1 = γn.pre.length + 1 by simp [hp0, ha0]]
        iexact Hrac
      have hgn : γr.raft.raft = γn.node := by rw [← HEγr, ← hρ]; exact hnd0
      have hJ := run_job_bodyR hAB ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩
        ⟨0, A₀⟩ A ce C hM hRB ap_ptr
        apv.entries' ceL apv.raftAdvancedC' apv.notifyc' γs (rnDv γn ce) γnc hidx hok rfl hdvn hdvs
        γn.key ha0 Hdisk γn apv.raftTerm' hgn.symm Hc0a.1
        (by have h := hpre.symm.trans hp0; rw [← HEγr, ← hρ]; exact h) rfl (token γwp)
      -- (R2d'a A7, A10 item 5) no merged send at the batch's term while the window is left: past it
      -- nothing; inside it `Hwpend`'s wand at `t0 < rt`, the token borrowed
      ihave #Hwnm : winNoMergedSendR γr.raft.raft s γn.t0 (token γwp)
          (A₀.drop (A ++ ce).length) apv.raftTerm' $$ []
      · iunfold winNoMergedSendR
        by_cases hw : A₀.drop (A ++ ce).length = []
        · ileft; ipureintro; exact hw
        · iright
          iintro !> %hlt Hwtk %id %m %st #Hwid Hwmo #Hwsm
          have hn : (rnLogOf γn (A ++ ce)).length < γn.a0.length := by
            rw [Ha0]
            have h1 : ¬ (A₀.length ≤ (A ++ ce).length) := fun h => hw (List.drop_eq_nil_iff.2 h)
            simp only [rnLogOf, hp0, List.nil_append, List.length_map]
            omega
          iapply Hwpw $$ %apv.raftTerm' %(rnLogOf γn (A ++ ce)).length Hwtk %(And.intro hn hlt) Hrtok %id %m %st
            Hwid Hwmo Hwsm
      ihave #Hmsinv' : (letI : MemStorReg GF := ⟨γr.raft.raft.reg⟩;
          memStorInv γn.ms γn.γs γr.raft.raft.cl γn.key) $$ []
      · iExactEq Hmsinv; rw [hgn, ← Hmsγ]
      simp only [run_job_bodyR_match] at hJ
      iapply hJ $$ [Hrun Hres Hnrc Hdv Hrh Hwp]
      · iframe #
        iframe Hrun Hres Hnrc Hdv Hrh Hwp
        rw [← Hsnap]; iexact snapshotA
      inext
      iintro ⟨Hrun, Hwp, Hres, Hrh⟩
      ihave Hhalf := Hrhb $$ Hrh
      wp_auto
      iapply HΦj
      iframe
    -- `sched.Schedule(f)`, tracked: `Q` the job's `Prev`, its `Post` saved as `post`
    wp_apply hSch sci γs j iprop(R ∗ notifyRcv γnc ∗ dvView ρ.raft (rnDv γn ce) (ghostOf ⟨0, A₀⟩ A)) Q
        iprop(applyResR C ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩ ⟨0, A₀⟩ (A ++ ce) ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half) ∗ token γwp) (some (Ps, pl, post))
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
      iprop(applyResR C ⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩ ⟨0, A₀⟩ (A ++ ce) ∗ (letI := srvStor (GF := GF) γn.node; nodeRunning γn.nl γn.node.cl srvClusterN (1 : Qp).half) ∗ token γwp), iprop(True)
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    iframe
    iframe #
    iunfold named
    iintro !> ⟨H, -⟩
    iexact H
  -- `leases := <-expiredLeaseC` (the lease-expiry plan's X1, 2026-11-04; until then dead in every
  -- mode): a slice of expired leases under the server's grant guard (`lessorOk`), so the cluster
  -- grants leases and auth is off; by the lease mode (`lease.runCfg`): `none` grants none (dead),
  -- `mono` lets none expire (dead: `leasesNoExpiry`), `revocable` revokes them
  -- (`revokeExpiredLeases`, through the open premise `srvRevokeOpen`)
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
    iintro %ls ⟨%Hnx, #Hls⟩
    ihave %Hg := srvGrantGuard_expired E.lg E.authMode.isOn ls $$ Hls
    ihave %Hlgt := isServerC_lg C s γ ci TM E ρ γr $$ Hsrv
    have hCoff : C.isOn = false := by
      have h2 := Hg.2
      rw [hM, AuthC.mode_isOn] at h2
      exact h2
    obtain ⟨mo, Hmo⟩ := Hslg
    cases mo with
    | none =>
      have h1 : γr.kv.lg = false := by rw [KVNames.lg_eq, lease.runCfg_lm Hmo]; rfl
      have h2 := Hlgt.2 hCoff
      iexfalso; ipureintro
      rw [h1, Hg.1] at h2
      exact Bool.false_ne_true h2
    | mono =>
      iexfalso; ipureintro
      exact Hnx (lease.runCfg_noExpiry Hmo)
    | revocable =>
      -- (revoke-open, 2026-11-06) the revocation with `#Hrvk` and the loop's thread token
      obtain ⟨hlev, hrevo⟩ := lease.runCfg_revoke Hmo
      have hrev := srvRevokeOpen_spec hrevo
      have hlm : ρ.rd.kv.lm = .revocable := by rw [Hlgt.1]; exact lease.runCfg_lm Hmo
      ihave #Hfa : srvFieldsAt s γ ci TM E ρ fv $$ []
      · rw [← srvFieldsAtM_false, ← hCoff]; iexact Hfv
      ihave #Hpe : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
      · iPkgInit
      (try wp_auto)
      wp_apply hrev s γ ci TM E ρ fv γr γg γcx v _ ls $$ [Htok] as Htok
      · iframe #; iframe Htok
        ipureintro; exact ⟨hlm, hlev⟩
      (try wp_auto)
      wp_for_post
      iframe
      iexists A, Ps, pl, Q, R
      iframe
      iframe #
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
  -- `<-s.stop`: a stop request (`srvStopReq`, `HardStop`'s; R2c-4: until then nothing was sent on
  -- it, D19m): `run` returns, and its deferred shutdown runs (below)
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
    iintro %u HSP
    -- (R2b-3d stage 5d) a stop request: `run` returns, and its deferred shutdown runs, with the
    -- stop's slot (R2c-4: `isServerRunC`'s) and the request's readers (R2c-4: until then
    -- `srvShutdownPre`'s)
    iunfold srvStop.slot at Hskeep
    icases Hskeep with ⟨%cfg, %γk, Hkeep, %hST⟩
    iunfold srvStopReq at HSP
    icases HSP with ⟨#HSP, %hsc, #Hdd, Hrds⟩
    obtain ⟨hoff, hcmp⟩ := hsc
    (try wp_auto)
    wp_for_post
    -- the deferred shutdown: `wgMu.Lock(); close(s.stopping); wgMu.Unlock()`
    ihave #Hgok' := Hgok
    iunfold srvGoAttachOk at Hgok'
    icases Hgok' with ⟨%chs, %cx, #Hchs, #Hint, #Hwg, #Hinv, #Hguard, -, -, -⟩
    wp_apply sync.RWMutex.wp_Lock_guard (srvWgMuAddr s) (wgMuP γg) $$ [$Hsync $Hguard]
      as ⟨Hlk, HwP⟩
    iunfold wgMuP at HwP
    icases HwP with ⟨%bo, Hbo, Hsp⟩
    imod goAttach_close γg bo $$ [$Hinv $Hclose $Hbo] with ⟨%hbo, Hbo, Hwz, Hwwt⟩
    subst hbo
    iunfold stopPart at Hsp
    simp only [↓reduceIte]
    (try wp_auto)
    wp_apply wp_stop_chan_close_at chs γg.ch γg.chi iprop(True) $$ [$Hint $Hsp] as #Hsd
    · imodintro; itrivial
    (try wp_auto)
    wp_apply sync.RWMutex.wp_Unlock_guard (srvWgMuAddr s) (wgMuP γg) $$ [$Hsync $Hlk Hbo]
    · iunfold wgMuP; iexists false; iframe Hbo; iunfold stopPart
      simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hsd
    -- `s.cancel()`
    (try wp_auto)
    wp_bind (App (Val #v.cancel) (Val #()))
    ihave #Hcfs' := Hcfs
    iunfold context.cancelSpec at Hcfs'
    iapply Hcfs' $$ []
    · imodintro; itrivial
    inext
    iintro -
    -- `sched.Stop()`: the last job's post, `Q`, and with the loop's `R` the apply thread's resources
    wp_auto_lc 3
    wp_apply +noauto hSStop sci γs (Ps ++ [pl]) $$ [Hstoptok Hq] as ⟨HlastP, -⟩
    · iframe Hstoptok Hq; iframe #; iapply schedule.schedPay_true $$ Hpay
    rw [List.getLast?_concat]
    icases HlastP with ⟨%P, #HP, HPl⟩
    iunfold schedule.savedProp at HP Hpl
    ihave #Heq := saved_prop_agree pl DFrac.discard DFrac.discard P Q $$ HP Hpl
    ihave HQl : ▷ Q $$ [HPl]
    · inext
      ihave Hiff := internalEq_iff _ _ $$ Heq
      icases Hiff with ⟨Hiff, -⟩
      iapply Hiff $$ HPl
    imod (lc_fupd_elim_later (E := ⊤) (P := Q)) $$ Hlc1 HQl with HQ
    ihave ⟨Hres, Hrunh, -⟩ := HQR $$ [HQ HR]
    · iframe HQ HR
    -- `s.wg.Wait()`
    (try wp_auto)
    wp_apply wp_goAttach_Wait s γg $$ [$Hsync $Hwg $Hinv $Hwz $Hwwt] as Hgw
    -- (R2d'a A10 item 3) inside the replay window the restart form (`StopR.lean`), past it the
    -- frozen path (`applyResR_past`)
    by_cases hwin : A.length < A₀.length
    · -- `s.r.stop()`: the WAL's apply half, the transport's stop right (`Er.ST`), the stop claim
      icases stop_splitR C _ ⟨0, A₀⟩ A $$ Hres with ⟨Hwta, Htrs, Hres⟩
      icases (srvStop.keep_split s cfg E γn γk) $$ Hkeep with ⟨Hrp, Hclp, Hcsp, Himp⟩
      icases srvStop.raft_stop s γn γk $$ [$Hrp $Htrs] with ⟨Hsc, HST⟩
      rw [← hST]
      (try wp_auto)
      wp_apply hRStop Er γn (srvRAddr s) A $$ [$Hpkg $Hrn $HST $Hrunh $Hwta $Hsc $Happly]
        as ⟨Hvac, %S, %σ, HrS, Hwc, %Hsh, #Hwcert⟩
      -- the records' commit at least `|A₀|`, from the restart data (`rnRestartOk_commit`)
      ihave ⟨HrS, %Hcm⟩ := rnRestartOk_commit γn S σ Hsh.1 $$ Hrok HrS
      ihave Hrst : iprop(∃ (S : RaftState) (σ : StorContents), raftState γn.node.cl γn.id S ∗
          rnWalClosed γn (srvRAddr s) σ ∗
          ⌜StorageHolds S σ ∧ σ.b ≤ (γn.pre ++ A).length ∧ A₀.length ≤ σ.commit⌝ ∗
          walSnapCert γn.node.cl σ) $$ [HrS Hwc]
      · iexists S, σ
        iframe HrS Hwc Hwcert
        ipureintro; exact ⟨Hsh.1, Hsh.2.1, by rw [← Ha0]; exact Hcm⟩
      -- `s.Cleanup()`: the backend closed, the image at the backend's log `A₀`
      (try wp_auto)
      wp_apply hClR C
          (⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩ : ApplyCtx GF)
          ⟨0, A₀⟩ A Er γg γcx v _ TM cfg dd hM hoff ⟨HEC, HEγr, Hc0a⟩ Hdisk hcmp hwin
        $$ [$Hpkg $Hsrv $Hrn $Hrf $Hres $HlbA $Hclp $Hcsp $Himp $Hdd $Hrds $HSP $Hvac $Hrst $HWB $Hsa
          Hlc2 Hlc3 $HWreg $Hgw] as Himg
      · iapply (lc_split (n := 1) (m := 1)).2; iframe Hlc2 Hlc3
      -- `close(s.done)`, the image escrowed (`srvDoneInv`)
      imod inv_alloc srvStopN ⊤ iprop(srvDiskImage ρ.rd.raft.raft ρ γn.id dd ∨ token c) $$ [Himg]
        with #Hdi
      · inext; ileft; iexact Himg
      (try wp_auto)
      wp_apply +noauto wp_broadcast_chan_close _ γd (srvDoneInv ρ.rd.raft.raft ρ γn.id dd c) $$ [$Hdc]
        as -
      · imodintro; iunfold srvDoneInv; iexact Hdi
      (try wp_auto)
      iapply HΦ
      iexact Htok
    -- past the window: `applyResC` (`applyResR_past`), the frozen path
    ihave Hres := applyResR_past C _ ⟨0, A₀⟩ A (by simp only; omega) $$ Hres
    -- `s.r.stop()`: the WAL's apply half, the transport's stop right (`Er.ST`), the stop claim
    icases stop_split C _ A $$ Hres with ⟨Hwta, Htrs, Hres⟩
    icases (srvStop.keep_split s cfg E γn γk) $$ Hkeep with ⟨Hrp, Hclp, Hcsp, Himp⟩
    icases srvStop.raft_stop s γn γk $$ [$Hrp $Htrs] with ⟨Hsc, HST⟩
    rw [← hST]
    (try wp_auto)
    wp_apply hRStop Er γn (srvRAddr s) A $$ [$Hpkg $Hrn $HST $Hrunh $Hwta $Hsc $Happly]
      as ⟨Hvac, Hrst⟩
    -- `s.Cleanup()`: the backend closed, the image
    (try wp_auto)
    wp_apply hCl C
        (⟨s, ep_ptr, γ, ci, b, E, γr, ai₀, c₀, x₀, ρ.wait, γn.ms, γn.γs, γp, ρ, γn⟩ : ApplyCtx GF)
        A Er γg γcx v _ TM cfg dd hM hoff ⟨HEC, HEγr, Hc0a⟩ Hdisk hcmp
      $$ [$Hpkg $Hsrv $Hrn $Hrf $Hres $Hclp $Hcsp $Himp $Hdd $Hrds $HSP $Hvac $Hrst $HWB $Hsa
        Hlc2 Hlc3 $HWreg $Hgw] as Himg
    · iapply (lc_split (n := 1) (m := 1)).2; iframe Hlc2 Hlc3
    -- `close(s.done)`, the image escrowed (`srvDoneInv`)
    imod inv_alloc srvStopN ⊤ iprop(srvDiskImage ρ.rd.raft.raft ρ γn.id dd ∨ token c) $$ [Himg]
      with #Hdi
    · inext; ileft; iexact Himg
    (try wp_auto)
    wp_apply +noauto wp_broadcast_chan_close _ γd (srvDoneInv ρ.rd.raft.raft ρ γn.id dd c) $$ [$Hdc]
      as -
    · imodintro; iunfold srvDoneInv; iexact Hdi
    (try wp_auto)
    iapply HΦ
    iexact Htok
  iapply BigAndL.bigAndL_nil.2
  itrivial


end proof

end EtcdGrove
end Perennial
