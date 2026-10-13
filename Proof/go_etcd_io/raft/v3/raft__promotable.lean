/-
Port of `election_proof/proof_raft__promotable.v`.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__promotable
public import Spec.go_etcd_io.raft.v3.raftLog__hasNextOrInProgressSnapshot

@[expose] public section

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

/-- `promotable` is

    pr := r.trk.Progress[r.id]
    return pr != nil && !pr.IsLearner && !r.raftLog.hasNextOrInProgressSnapshot()

Goose renders each `&&` as `If e1 e2 #false`, so the proof splits on whether `r.id`
is a voter, which by the tracker's domain fact is whether it is in the progress map:

- `id ∈ cfg`: `wp_tracker_progress_lookup` hands out that voter's `ownProgress`, whose
  `pr ↦ pv` makes `pr ≠ nil` and whose not-a-learner fact makes `!pr.IsLearner` true;
  the callee returns `!snap.isSome` under `ownRaftLog`.
- `id ∉ cfg`: the lookup yields `nil`, so the first conjunct is `false` and the rest
  is never evaluated. Result `false`.

`r.id` and `r.raftLog` are read with their field lemmas; the map `r.trk.Progress` is
read off the tracker object that `ownRaftPhys_tracker_same` hands out, and the log's
method runs on what `ownRaftPhys_log_same` hands out. Nothing is written to `r`. -/
theorem raft.promotable.wp_proof
    (wp_raftLog_hasNextOrInProgressSnapshot :
      raftLog.hasNextOrInProgressSnapshot.spec (GF := GF) (hG := hG)) :
    raft.promotable.spec (GF := GF) (hG := hG) := by
  intro cfg r id s
  wp_start as Hphys
  wp_auto
  wp_apply raft.wp_load_id $$ Hphys as Hphys
  icases ownRaftPhys_tracker_same cfg r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  icases ownTracker_flags cfg tv _ $$ Htrk with ⟨%Hfl, Htrk⟩
  wp_auto
  by_cases Hin : id ∈ cfg
  · -- a voter: its `Progress` is in the map and is not a learner's
    wp_apply wp_tracker_progress_lookup cfg tv _ id Hin $$ Htrk
      as %pr ⟨%Hlk, %p, %Hpv, Hpr, Hprback⟩
    iNamed Hpr
    have Hnolearner : pv.IsLearner' = false := by
      rw [((progressAbs_Some _ _ _).1 Habs).1, Hfl id p Hpv]
      exact decide_eq_false (fun h => h Hin)
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hpv
    -- `wp_auto` already reduced `pr != nil` to `!decide (pr = null)`
    simp only [decide_eq_false Hnn, Bool.not_false]
    wp_auto
    rw [Hnolearner]
    wp_auto
    ihave Htrk := Hprback $$ %p [Hpv Hinfl] %rfl
    · iapply ownProgress_intro $$ Hpv Hinfl %Habs
    -- written back at the values it was read at
    simp only [GMap.insert_id s.prvals id p Hpv]
    ihave Hphys := Hback $$ Htrkf Htrk
    wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
    icases ownRaftPhys_log_same cfg r id s $$ Hphys with ⟨Hlog, Hback⟩
    wp_apply wp_raftLog_hasNextOrInProgressSnapshot $$ [$Hlog] as %hb ⟨Hlog, %Hhb⟩
    subst hb
    ihave Hphys := Hback $$ Hlog
    iapply HΦ
    iframe Hphys
    ipureintro
    cases s.logst.snap <;> simp [Hin]
  · icases ownTracker_progress_map cfg tv _ $$ Htrk with ⟨#Hprs, %Hdom, Htrk⟩
    cases Hlk : s.progress !! id with
    | some pr =>
      -- a learner (2026-10-13): `!pr.IsLearner` short-circuits to false
      wp_apply wp_map_lookup1 go.uint64 (go.GoType.PointerType tracker.Progress.ty) _ s.progress
        id _ $$ Hprs with -
      rw [Hlk]
      simp only [Option.getD_some]
      icases ownTracker_lookup cfg tv _ id pr Hlk $$ Htrk with ⟨%p, %Hpv, Hpr, Hprback⟩
      iNamed Hpr
      have Hl : pv.IsLearner' = true := by
        rw [((progressAbs_Some _ _ _).1 Habs).1, Hfl id p Hpv]
        exact decide_eq_true Hin
      ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hpv
      simp only [decide_eq_false Hnn, Bool.not_false]
      wp_auto
      rw [Hl]
      wp_auto
      ihave Htrk := Hprback $$ %p [Hpv Hinfl] %rfl
      · iapply ownProgress_intro $$ Hpv Hinfl %Habs
      simp only [GMap.insert_id s.prvals id p Hpv]
      ihave Hphys := Hback $$ Htrkf Htrk
      iapply HΦ
      iframe Hphys
      ipureintro
      simp [Hin]
    | none =>
    -- not tracked: the lookup misses, `pr == nil` short-circuits to false
    have Hnone : s.progress !! id = none := Hlk
    -- the progress map is read-only, so it stays in the persistent context
    wp_apply wp_map_lookup1 go.uint64 (go.GoType.PointerType tracker.Progress.ty) _ s.progress
      id _ $$ Hprs with -
    rw [Hnone]
    simp only [Option.getD_none]
    wp_auto
    ihave Hphys := Hback $$ Htrkf Htrk
    iapply HΦ
    iframe Hphys
    ipureintro
    simp [Hin]

end proof

end EtcdGrove
end Perennial
