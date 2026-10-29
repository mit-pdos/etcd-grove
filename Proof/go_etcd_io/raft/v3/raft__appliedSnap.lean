/- (D22 S-d2, 2026-10-21) Lean-first.

(2026-10-28, stage U0) The tracker's rebuild from the snapshot's `ConfState`, moved here from
`raft__restore.lean` with the code (`raft37-goose-lean-a2`). -/
module

public import Spec.go_etcd_io.raft.v3.raft__appliedSnap
public import Spec.go_etcd_io.raft.v3.raft__appliedTo
public import Spec.go_etcd_io.raft.v3.raftLog__stableSnapTo
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Spec.go_etcd_io.raft.v3.raftLog__lastIndex
public import Spec.go_etcd_io.raft.v3.tracker.MakeProgressTracker
public import Spec.go_etcd_io.raft.v3.confchange.Restore
public import Spec.go_etcd_io.raft.v3.raft__switchToConfig
public import Spec.go_etcd_io.raft.v3.assertConfStatesEquivalent
public import Spec.go_etcd_io.raft.v3.raftpb.EnsureConfState
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetConfState
public import Proof.go_etcd_io.raft.v3.LemmasSnapCfg
public import Proof.go_etcd_io.raft.v3.LemmasSendRD

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The index through the getters; `stableSnapTo` on the log in the windows, then `appliedTo`,
whose premises the log gives: the snapshot at or below the boundary, which is at most `committed`
and below `offsetInProgress` (`ownRaftLogW_struct`), and on a hit the boundary itself (the pending
snapshot is `prev`, `ownRaftLogW_snap_prev`), so `appliedSnap`'s window ends there. Then (stage U0)
the rebuild, as `restore` ran it until then: the conf state read and `EnsureConfState`d
(`wp_EnsureConfState_opt`: frozen with its `AutoLeave` set), the tracker replaced by the empty one
`MakeProgressTracker` builds (`ownRaftPhysC_retrack`, `ownTrackerC_empty`; the tally was already
empty), `confchange.Restore` on it (`restoreM_wf`), `switchToConfig` to the snapshot's
configuration and `assertConfStatesEquivalent`. -/
theorem raft.appliedSnap.wp_proof
    (wp_raftLog_stableSnapTo : raftLog.stableSnapTo.spec (GF := GF) (hG := hG))
    (wp_raft_appliedTo : raft.appliedTo.spec (GF := GF) (hG := hG))
    (wp_Snapshot_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_SnapshotMetadata_GetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_MakeProgressTracker : tracker.MakeProgressTracker.spec (GF := GF) (hG := hG))
    (wp_confchange_Restore : confchange.Restore.spec (GF := GF) (hG := hG))
    (wp_raft_switchToConfig : raft.switchToConfig.spec (GF := GF) (hG := hG))
    (wp_assertConfStatesEquivalent : assertConfStatesEquivalent.spec (GF := GF) (hG := hG))
    (wp_EnsureConfState : raftpb.EnsureConfState.spec (GF := GF) (hG := hG))
    (wp_SnapshotMetadata_GetConfState :
      raftpb.SnapshotMetadata.GetConfState.spec (GF := GF) (hG := hG)) :
    raft.appliedSnap.spec (GF := GF) (hG := hG) := by
  intro c r id s sp sv cl Hiff Haps Hle Hrole Hvotes Hcl Hscope Hun Hns Hsx Hkx
  subst Hcl
  obtain ⟨Hwf, Hvnd, Hlnd, Hond, Hnnd, Hsz, Hal0, -⟩ := Hscope
  wp_start as H
  iNamed H
  wp_auto
  wp_apply wp_Snapshot_GetMetadata.1 sp _ sv $$ [$Hsnap] as %pm ⟨Hm, Hback⟩
  wp_apply wp_SnapshotMetadata_GetIndex pm _ _ $$ [$Hm] as Hm
  ispecialize Hback $$ Hm
  try wp_auto
  -- `r.raftLog.stableSnapTo(index)`
  wp_apply raft.wp_load_raftLogCW $$ Hphys as Hphys
  icases ownRaftPhysCVW_log_at c r id s $$ Hphys with ⟨Hlog, %Hgh0, Hlogback⟩
  icases ownRaftLogW_snap_prev _ _ $$ Hlog with ⟨%Hsp, Hlog⟩
  wp_apply wp_raftLog_stableSnapTo _ _ _ Hiff $$ [$Hlog] as Hlog
  icases ownRaftLogW_struct _ _ $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
  ihave Hlog := Hlb $$ Hl
  obtain ⟨Hpv1, Hse1, Hue1, -, -, -, -, -, -, Hst1, -, -, -, -, -⟩ :=
    logStableSnap_fields s.logst sv.Metadata'.Index'
  obtain ⟨-, -, -, Hpc, Hpi⟩ := Hlv
  rw [Hpv1] at Hpc Hpi
  have Hkeep : LogNsKeep s (logStableSnap s.logst sv.Metadata'.Index') := by
    intro h
    rw [logStableSnap_none _ _ (Hns h)]
    exact ⟨rfl, rfl, rfl, Int.le_refl _⟩
  ihave Hphys := Hlogback $$ %_ Hlog %(LogGhOk.of_off Hun Hkeep (SnpOk.stableSnap _ Hgh0.1.2.1) ((logStableSnap_sn _ _).trans Hgh0.1.2.2) Hst1)
    %(fun _ => logLast_le_of_fields (by rw [Hpv1]) (by rw [Hse1]) (by rw [Hue1]))
  -- `r.appliedTo(index, 0)`
  have Hsa1 : (logStableSnap s.logst sv.Metadata'.Index').sapp = false := by
    unfold logStableSnap
    split
    · rfl
    · rename_i h
      cases h' : s.logst.sapp
      · rfl
      · exact absurd (Hiff.2 h') h
  have Haps1 : (logStableSnap s.logst sv.Metadata'.Index').aps = true →
      uint.Z (logStableSnap s.logst sv.Metadata'.Index').prev.index' ≤ uint.Z sv.Metadata'.Index' := by
    intro h
    rw [Hpv1]
    cases Hh : snapHit s.logst.snap sv.Metadata'.Index'
    · rw [logStableSnap_miss _ _ Hh, Haps] at h; cases h
    · cases Hs : s.logst.snap with
      | none => rw [Hs] at Hh; cases Hh
      | some sid =>
        rw [Hs] at Hh
        simp only [snapHit, decide_eq_true_eq] at Hh
        rw [← Hsp sid Hs, Hh]
        exact Int.le_refl _
  have Hsx1 : (logStableSnap s.logst sv.Metadata'.Index').snap ≠ none →
      (logStableSnap s.logst sv.Metadata'.Index').lent = false →
      uint.Z (logStableSnap s.logst sv.Metadata'.Index').applying < uint.Z sv.Metadata'.Index' →
      uint.Z sv.Metadata'.Index' ≤ uint.Z (logStableSnap s.logst sv.Metadata'.Index').sxt := by
    intro h1 h2 _
    cases Hh : snapHit s.logst.snap sv.Metadata'.Index'
    · rw [logStableSnap_miss _ _ Hh] at h1 h2 ⊢; exact Hsx h1 h2
    · exfalso; apply h1; unfold logStableSnap; simp [Hh]
  -- (D22 S-r) a pending snapshot the acknowledgement misses is past it: the boundary, at least
  -- the acknowledged index, is the pending snapshot, of another index
  have Hsp1 : (logStableSnap s.logst sv.Metadata'.Index').snap ≠ none →
      (logStableSnap s.logst sv.Metadata'.Index').sip = false →
      uint.Z (logStableSnap s.logst sv.Metadata'.Index').applying < uint.Z sv.Metadata'.Index' →
      uint.Z sv.Metadata'.Index' < uint.Z (logStableSnap s.logst sv.Metadata'.Index').prev.index' := by
    intro h1 _ _
    cases Hh : snapHit s.logst.snap sv.Metadata'.Index'
    · rw [logStableSnap_miss _ _ Hh] at h1 ⊢
      obtain ⟨sid, Hs⟩ := Option.ne_none_iff_exists'.1 h1
      rw [Hs] at Hh
      simp only [snapHit, decide_eq_false_iff_not] at Hh
      have Hpe := Hsp sid Hs
      have Hne : uint.Z sv.Metadata'.Index' ≠ uint.Z sid.index' := by
        intro h; apply Hh; word
      rw [← Hpe] at Hle ⊢
      omega
    · exfalso; apply h1; unfold logStableSnap; simp [Hh]
  -- (2026-10-29, stage U5) at a follower `appliedTo` proposes no leave: its leader-only premises
  -- are vacuous, its receipt any (`⧖ 0`), and it ends at the new `applied`
  have Hnl : ∀ {P : Prop}, ({ s with logst := logStableSnap s.logst sv.Metadata'.Index' } : NState).role
      = .leader → P := fun h => absurd (Hrole.symm.trans h) (by decide)
  imod preceipt_zero (GF := GF) with #Hrc0
  wp_apply wp_raft_appliedTo c r id { s with logst := logStableSnap s.logst sv.Metadata'.Index' }
      sv.Metadata'.Index' (W64 0) 0 (by simp only; omega) (fun _ => by simp only; omega)
      Hnl Hnl Hnl Hsa1 Haps1
      Hsx1 Hsp1 (fun _ k hk => Hkx k hk) $$ [$Hphys $Hrc0] as %s2' %B %recv ⟨Hphys, %Hls, -⟩
  rcases Hls with ⟨rfl, -⟩ | ⟨-, Hl, -⟩
  case inr => exact absurd (Hrole.symm.trans Hl) (by decide)
  -- (U0) `cs := pb.EnsureConfState(snap.GetMetadata().GetConfState())`: the set snapshot's conf
  -- state, its `AutoLeave` already set
  generalize HS2 : ({ s with logst := logAppliedTo (logStableSnap s.logst sv.Metadata'.Index') sv.Metadata'.Index' (W64 0) } : NState) = s2
  have Hrole2 : s2.role = .follower := by rw [← HS2]; exact Hrole
  icases ownRaftPhysC_log_at c r id s2 $$ Hphys with ⟨Hlog, %Hgh2, Hlogback⟩
  ihave Hphys := Hlogback $$ Hlog %Hgh2 %(fun h => absurd (Hrole2.symm.trans h) (by decide))
  try wp_auto
  wp_apply wp_Snapshot_GetMetadata.1 sp _ sv $$ [$Hback] as %pm2 ⟨Hm, Hback⟩
  wp_apply wp_SnapshotMetadata_GetConfState pm2 _ _ $$ [$Hm] as %pc ⟨Hcs, Hmb⟩
  try wp_auto
  wp_apply wp_EnsureConfState_opt wp_EnsureConfState pc _ $$ [Hcs] as %q ⟨#Hcf, Hcs, -⟩
  · iexact Hcs
  ihave Hm := Hmb $$ Hcs
  ihave Hback := Hback $$ Hm
  try wp_auto
  -- the tracker replaced by the empty one, the log used meanwhile
  icases ownRaftPhysC_retrack c c.voters (CfgM.simple ∅ ∅).voters
      (c := CfgM.simple ∅ ∅) _ _ _
      (by intro h; exact absurd Hrole2 h) $$ Hphys with ⟨%tv, Htrkf, Htrk, Hlf, Hlog, Hback⟩
  icases ownTrackerC_maxinflight $$ Htrk with ⟨%Hmi, -⟩
  wp_auto
  wp_apply wp_MakeProgressTracker as %tv0 %v0 ⟨%Htv0, Hv0, Hvotes0, Hprs0⟩
  obtain ⟨Htv0mi, Htv0mb, Htv0arr, Htv0l, Htv0ln, Htv0al⟩ := Htv0
  wp_apply wp_raftLog_lastIndex $$ [$Hlog] as %li ⟨Hlog, -⟩
  -- `confchange.Restore`: the empty tracker, the snapshot's `ConfState`, which it answers
  -- exactly (`restoreM_wf`)
  ipersist Hprs0
  have Hmi0 : 0 ≤ sint.Z tv0.MaxInflight' ∧ sint.Z tv0.MaxInflight' < 2 ^ 62 := by
    rw [Htv0mi]; exact Hmi
  have Hvne : sv.Metadata'.ConfState'.lists.voters ≠ [] := Hwf.1
  have Hrm := restoreM_wf sv.Metadata'.ConfState'.lists.outgoing sv.Metadata'.ConfState'.lists.voters sv.Metadata'.ConfState'.lists.learners sv.Metadata'.ConfState'.lists.learnersNext
    sv.Metadata'.ConfState'.AutoLeave' Hwf
  have Hinv := restoreM_cfgInv Hrm
  ihave HcB := csPts_weaken $$ Hcf
  wp_apply wp_confchange_Restore { Tracker' := tv0, LastIndex' := li } q sv.Metadata'.ConfState'
      _ v0 _ Hrm Hmi0 Htv0arr Htv0l Htv0ln Htv0al
      $$ [$HcB $Hv0 $Hprs0]
    as %cfgv %prsm %prs ⟨HcB, Hv0, -, Hres⟩
  -- a voter, so an op ran: the fresh maps (2026-10-16, stage R8b)
  icases Hres with (⟨%Hops, -⟩ | ⟨-, Hcfg, Hprsm, %Hprs, Hprogs⟩)
  · exfalso; exact restoreSimpleOps_ne_nil_of_voters _ _ _ _ Hvne Hops
  -- the configuration `Restore` built, as `switchToConfig` takes it
  ipersist Hprsm
  have Hsz' : (GMap.size prs : Int) ≤ 2 ^ 62 :=
    restore_prs_size sv.Metadata'.ConfState'.lists Hvnd Hlnd Hond Hsz prs sv.Metadata'.ConfState'.AutoLeave' Hprs
  ihave Hprogs : ([∗map] k ↦ pr ∈ prs, ∃ p, ownProgress (GF := GF) pr p ∗
      ⌜(cfgStateC (csCfgM sv.Metadata'.ConfState'.lists.outgoing sv.Metadata'.ConfState'.lists.voters sv.Metadata'.ConfState'.lists.learners sv.Metadata'.ConfState'.lists.learnersNext
        sv.Metadata'.ConfState'.AutoLeave')).prs !! k = some p.learner⌝) $$ [Hprogs]
  · iapply BigSepM.bigSepM_mono ?_ $$ Hprogs
    intro k pr _
    iintro ⟨%p, Hp, %Hpk⟩
    iexists p
    iframe Hp
    ipureintro
    simpa [cfgStateC, cfgFlags, csCfgM, CfgM.voters, ConfStateM.lists] using Hpk
  ihave Hcfg := ownCfgCC_cast cfgv _
    (csCfgM sv.Metadata'.ConfState'.VotersOutgoing' sv.Metadata'.ConfState'.Voters' sv.Metadata'.ConfState'.Learners' sv.Metadata'.ConfState'.LearnersNext' sv.Metadata'.ConfState'.AutoLeave')
    (snapCfg sv sv.Metadata'.ConfState'.lists) rfl $$ Hcfg
  icases ownConfigC_of_restore (snapCfg sv sv.Metadata'.ConfState'.lists) cfgv prsm prs Hinv Hprs Hsz' _ (fun _ _ h => h) $$ Hcfg Hprsm Hprogs
    with ⟨%pvs, Hnew⟩
  -- the struct, re-sealed over the empty configuration
  ihave Htrk0 := ownTrackerC_empty tv0 v0 Htv0arr Htv0l Htv0ln Htv0al Hmi0 $$ Hv0 Hvotes0 Hprs0
  ihave Hphys := Hback $$ %tv0 %∅ %∅ %∅ %_ Hlf Htrkf Htrk0 Hlog %Hgh2
    %(PrvalsOk.not_leader (fun h => absurd (Hrole2.symm.trans h) (by decide)))
  generalize HS1 : ({ s2 with votes := ∅, progress := ∅, prvals := ∅, logst := s2.logst } : NState) = s1
  have Hrole1 : s1.role = .follower := by rw [← HS1]; exact Hrole2
  -- `assertConfStatesEquivalent(r.logger, cs, r.switchToConfig(cfg, trk))`
  wp_apply raft.wp_load_loggerC $$ Hphys as %lok0 ⟨Hphys, #Hlg0⟩
  icases ownRaftPhysCV_reconfig _ (snapCfg sv sv.Metadata'.ConfState'.lists) ((snapCfg sv sv.Metadata'.ConfState'.lists).voters ∪ {[id]}) r id s1
      (fun h => absurd Hrole1 h) $$ Hphys with ⟨%tv1, Htrkf, Hold, Hback2⟩
  icases ownTrackerC_votes $$ Hold with ⟨Hvotes, %Hmi1⟩
  wp_apply wp_raft_switchToConfig (snapCfg sv sv.Metadata'.ConfState'.lists) r id s1 tv1 cfgv prsm prs pvs
      (fun h => absurd (Hrole1.symm.trans h) (by decide))
      (fun h => by rcases h with h | h <;> rw [Hrole1] at h <;> cases h)
      (fun h => absurd (Hrole1.symm.trans h) (by decide))
    $$ [$Htrkf $Hback2 $Hvotes $Hnew]
    as %cs2 %xs2 %os2 %ls2 %lns2 %s2 ⟨Hphys, Hcs2v, %Hcs2, %Hsw⟩
  · ipureintro; exact Hmi1
  obtain ⟨Hxs2, Hos2, Hls2, Hlns2⟩ := Hcs2
  unfold SwitchOkC at Hsw
  rw [ite_eq_right (by simp [Hrole1])] at Hsw
  subst Hsw
  -- the snapshot's lists against the configuration's sets
  have Hperm : sv.Metadata'.ConfState'.lists.Perm ⟨xs2, ls2, os2, lns2⟩ := by
    refine ⟨(perm_elements_listToSet _ Hvnd).trans Hxs2.symm,
      (perm_elements_listToSet _ Hlnd).trans Hls2.symm,
      (perm_elements_listToSet _ Hond).trans Hos2.symm,
      (perm_elements_listToSet _ Hnnd).trans Hlns2.symm⟩
  have Hbnd : sv.Metadata'.ConfState'.lists.Bounded := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  ihave Hcs2v := csPts_weaken $$ Hcs2v
  have Hal2 : sv.Metadata'.ConfState'.AutoLeave' = (snapCfg sv sv.Metadata'.ConfState'.lists).autoLeave := by
    unfold snapCfg csCfgM
    by_cases ho : sv.Metadata'.ConfState'.lists.outgoing = []
    · simp only [ho, ↓reduceIte]; exact Hal0 ho
    · simp only [ho, ↓reduceIte]
  wp_apply wp_assertConfStatesEquivalent _ q cs2 sv.Metadata'.ConfState'
      (ConfStateM.mk xs2 ls2 os2 lns2
        (if sv.Metadata'.ConfState'.VotersOutgoing' = [] then false else sv.Metadata'.ConfState'.AutoLeave')) _ _ Hperm Hbnd Hal2
      $$ [$HcB $Hcs2v] as ⟨HcB, -⟩
  iapply HΦ $$ %prs %pvs %(learnerOfC (snapCfg sv sv.Metadata'.ConfState'.lists) id)
  iframe Hback
  have Hs' : ({ s1 with progress := prs, prvals := pvs,
                        isLearner := learnerOfC (snapCfg sv sv.Metadata'.ConfState'.lists) id } :
        NState) =
      { s with logst := logAppliedTo (logStableSnap s.logst sv.Metadata'.Index') sv.Metadata'.Index' (W64 0),
               progress := prs, prvals := pvs,
               isLearner := learnerOfC (snapCfg sv sv.Metadata'.ConfState'.lists) id } := by
    subst HS1 HS2
    obtain ⟨⟩ := s
    simp only at Hvotes
    subst Hvotes
    rfl
  rw [← Hs']
  iexact Hphys

end proof

end EtcdGrove
end Perennial
