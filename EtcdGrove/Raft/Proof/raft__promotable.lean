/-
Port of `election_proof/proof_raft__promotable.v`.
-/
import EtcdGrove.Raft.Spec.raft__promotable
import EtcdGrove.Raft.Spec.raftLog__hasNextOrInProgressSnapshot

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
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
  wp_auto
  by_cases Hin : id ∈ cfg
  · -- a voter: its `Progress` is in the map and is not a learner's
    wp_apply wp_tracker_progress_lookup cfg tv _ id Hin $$ Htrk
      as %pr ⟨%Hlk, %p, %Hpv, Hpr, Hprback⟩
    iNamed Hpr
    have Hnolearner := ((progressAbs_Some _ _ _).1 Habs).1
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hpv
    -- `wp_auto` already reduced `pr != nil` to `!decide (pr = null)`
    simp only [decide_eq_false Hnn, Bool.not_false]
    wp_auto
    rw [Hnolearner]
    wp_auto
    ihave Htrk := Hprback $$ %p [Hpv Hinfl]
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
  · -- not a voter: the lookup misses, `pr == nil` short-circuits to false
    icases ownTracker_progress_map cfg tv _ $$ Htrk with ⟨#Hprs, %Hdom, Htrk⟩
    have Hnone : s.progress !! id = none := by
      cases h : s.progress !! id with
      | none => rfl
      | some v =>
        exact absurd (by rw [← Hdom, GMap.elem_of_dom]; exact ⟨v, h⟩) Hin
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
