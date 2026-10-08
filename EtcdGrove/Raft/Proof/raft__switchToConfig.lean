/-
Port of election_proof/proof_raft__switchToConfig.v.
-/
import EtcdGrove.Raft.Spec.raft__switchToConfig
import EtcdGrove.Raft.Spec.traceConfChangeEvent
import EtcdGrove.Raft.Spec.ProgressTracker__ConfState

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raft.switchToConfig.wp_proof
    (wp_traceConfChangeEvent : traceConfChangeEvent.spec (GF := GF) (hG := hG))
    (wp_ProgressTracker_ConfState : tracker.ProgressTracker.ConfState.spec (GF := GF) (hG := hG)) :
    raft.switchToConfig.spec (GF := GF) (hG := hG) := by
  intro cfg0 cfg r id s cfgv prsm prs Hrole
  wp_start as ⟨Hphys, Hnew⟩
  wp_auto
  wp_apply wp_traceConfChangeEvent
  -- `r.trk.Config = cfg; r.trk.Progress = trk`: the one change of configuration, through
  -- `ownRaftPhys_reconfig`
  icases ownRaftPhys_reconfig cfg0 cfg r id s $$ Hphys with ⟨%tv, Htrkf, Hold, Hback⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Htrkf with ⟨Htrkf, %Hnn⟩
  iStructNamed Htrkf
  wp_auto
  ihave Htrkf : r.[raft, go!"trk"] ↦
      ({ tv with Config' := cfgv, Progress' := prsm } : tracker.ProgressTracker)
      $$ [Votes MaxInflight MaxInflightBytes Config Progress]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  icases ownTracker_reconfig cfg0 cfg _ _ cfgv prsm prs $$ Hold Hnew with ⟨%pvs, Htrk⟩
  ihave Hphys := Hback $$ %_ %prs %pvs Htrkf Htrk
  -- the log line: `r.id`, `r.trk.Config`
  wp_apply raft.wp_load_id $$ Hphys as Hphys
  icases ownRaftPhys_tracker_same cfg r id _ $$ Hphys with ⟨%tv1, Htrkf, Htrk, Hback⟩
  wp_auto
  ihave Hphys := Hback $$ %tv1 Htrkf Htrk
  wp_raft_log
  -- `cs := r.trk.ConfState()`
  icases ownRaftPhys_tracker_same cfg r id _ $$ Hphys with ⟨%tv2, Htrkf, Htrk, Hback⟩
  wp_apply wp_ProgressTracker_ConfState $$ [$Htrkf $Htrk]
    as %cs %xs ⟨Htrkf, Htrk, Hcs, %Hxs, %Hcs0⟩
  ihave Hphys := Hback $$ %tv2 Htrkf Htrk
  -- `pr, ok := r.trk.Progress[r.id]`
  wp_apply raft.wp_load_id $$ Hphys as Hphys
  icases ownRaftPhys_tracker_same cfg r id _ $$ Hphys with ⟨%tv3, Htrkf, Htrk, Hback⟩
  icases ownTracker_progress_map cfg _ _ $$ Htrk with ⟨#Hprs, %Hdom, Htrk⟩
  wp_auto
  wp_apply wp_map_lookup2 $$ Hprs as -
  -- `r.isLearner = ok && pr.IsLearner` is `false`: every voter's `Progress` has
  -- `IsLearner = false`
  have Hns : stateW64 s.role ≠ W64 2 := by
    cases h : s.role <;> simp_all [stateW64, StateFollower, StateCandidate, StatePreCandidate]
  dsimp only
  cases Hlk : prs !! id with
  | some pr =>
    simp only [Option.getD_some, Option.isSome_some]
    wp_auto
    icases ownTracker_lookup_same cfg _ _ id pr Hlk $$ Htrk with ⟨%p, -, Hpr, Hprback⟩
    iNamed Hpr
    have Hnolearner := ((progressAbs_Some _ _ _).1 Habs).1
    wp_auto
    rw [Hnolearner]
    ihave Htrk := Hprback $$ [Hpv Hinfl]
    · iapply ownProgress_intro $$ Hpv Hinfl
      ipureintro; exact Habs
    ihave Hphys := Hback $$ %tv3 Htrkf Htrk
    wp_apply raft.wp_store_isLearner $$ Hphys as Hphys
    wp_apply raft.wp_load_isLearner $$ Hphys as Hphys
    wp_apply raft.wp_load_state $$ Hphys as Hphys
    rw [decide_eq_false Hns]
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    exact ⟨Hxs, Hcs0⟩
  | none =>
    simp only [Option.getD_none, Option.isSome_none]
    wp_auto
    ihave Hphys := Hback $$ %tv3 Htrkf Htrk
    wp_apply raft.wp_store_isLearner $$ Hphys as Hphys
    -- `!ok` is `true`: the `||` does not load `r.isLearner`, and `r.state` is loaded by
    -- both `if`s
    wp_apply raft.wp_load_state $$ Hphys as Hphys
    rw [decide_eq_false Hns]
    wp_auto
    wp_apply raft.wp_load_state $$ Hphys as Hphys
    rw [decide_eq_false Hns]
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    exact ⟨Hxs, Hcs0⟩

end proof

end EtcdGrove
end Perennial
