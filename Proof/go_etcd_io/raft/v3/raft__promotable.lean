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
read off the tracker object that `ownRaftPhysC_tracker_same` hands out, and the log's
method runs on what `ownRaftPhysC_log_same` hands out. Nothing is written to `r`. -/
theorem raft.promotable.wp_proof
    (wp_raftLog_hasNextOrInProgressSnapshot :
      raftLog.hasNextOrInProgressSnapshot.spec (GF := GF) (hG := hG)) :
    raft.promotable.spec (GF := GF) (hG := hG) := by
  intro c r id s
  wp_start as Hphys
  wp_auto
  wp_apply raft.wp_load_idC $$ Hphys as Hphys
  icases ownRaftPhysC_tracker_same c r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  icases ownTrackerC_pure c tv _ $$ Htrk with ⟨%Hpure, Htrk⟩
  obtain ⟨Hinv, Hdom, Hfl, -, -⟩ := Hpure
  dsimp only at Hinv Hdom Hfl
  icases ownTrackerC_progress_map c tv _ $$ Htrk with ⟨#Hprs, -, Htrk⟩
  wp_auto
  cases Hlk : s.progress !! id with
  | some pr =>
    wp_apply wp_map_lookup1 go.uint64 (go.GoType.PointerType tracker.Progress.ty) _ s.progress
      id _ $$ Hprs with -
    rw [Hlk]
    simp only [Option.getD_some]
    icases ownTrackerC_lookup c tv _ id pr Hlk $$ Htrk with ⟨%p, %Hpv, Hpr, Hprback⟩
    iNamed Hpr
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hpv
    simp only [decide_eq_false Hnn, Bool.not_false]
    wp_auto
    have Hl : pv.IsLearner' = decide (id ∈ c.learners) := by
      rw [((progressAbs_Some _ _ _).1 Habs).1, Hfl id p Hpv]
    have Htr : id ∈ c.ids := by
      rw [← Hdom, GMap.elem_of_dom]; exact ⟨pr, Hlk⟩
    by_cases Hin : id ∈ c.voters
    · -- a voter: not a learner (`CfgInv`)
      have Hnl : id ∉ c.learners := by
        intro h
        obtain ⟨h1, h2, -⟩ := Hinv.2.2.1 id h
        unfold CfgM.voters at Hin
        rcases (GMap.elem_of_union _ _ _).1 Hin with h' | h'
        · exact h2 h'
        · exact h1 h'
      rw [Hl, decide_eq_false Hnl]
      wp_auto
      ihave Htrk := Hprback $$ %p [Hpv Hinfl] %rfl
      · iapply ownProgress_intro $$ Hpv Hinfl %Habs
      simp only [GMap.insert_id s.prvals id p Hpv]
      ihave Hphys := Hback $$ Htrkf Htrk
      wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
      icases ownRaftPhysC_log_same c r id s $$ Hphys with ⟨Hlog, Hback⟩
      wp_apply wp_raftLog_hasNextOrInProgressSnapshot $$ [$Hlog] as %hb ⟨Hlog, %Hhb⟩
      subst hb
      ihave Hphys := Hback $$ Hlog
      iapply HΦ
      iframe Hphys
      ipureintro
      cases s.logst.snap <;> simp [Hin]
    · -- a learner (2026-10-13): `!pr.IsLearner` short-circuits to false
      have Hlr : id ∈ c.learners := by
        unfold CfgM.ids at Htr
        rcases (GMap.elem_of_union _ _ _).1 Htr with h' | h'
        · exact absurd h' Hin
        · exact h'
      rw [Hl, decide_eq_true Hlr]
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
    have Hin : id ∉ c.voters := by
      intro h
      have h2 : id ∈ domSet s.progress := by rw [Hdom]; exact voters_sub_ids c |> fun hs => (GMap.elem_of_subseteq _ _).1 hs _ h
      rw [GMap.elem_of_dom] at h2
      obtain ⟨x, hx⟩ := h2
      rw [Hnone] at hx; cases hx
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
