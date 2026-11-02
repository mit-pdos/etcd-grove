/- Lean-first (no Rocq counterpart, 2026-10-29, stage U7). -/
module

public import Spec.go_etcd_io.raft.v3.getStatus
public import Spec.go_etcd_io.raft.v3.getBasicStatus
public import Spec.go_etcd_io.raft.v3.getProgressCopy
public import Spec.go_etcd_io.raft.v3.tracker.Config__Clone

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The basic status, at a leader the progress copy, then the configuration's clone, read through
the tracker field (`ownRaftPhysC_tracker_same`, the `Config` field of `trk`). -/
theorem getStatus.wp_proof
    (wp_getBasicStatus : getBasicStatus.spec (GF := GF) (hG := hG))
    (wp_getProgressCopy : getProgressCopy.spec (GF := GF) (hG := hG))
    (wp_Config_Clone : tracker.Config.Clone.spec (GF := GF) (hG := hG)) :
    getStatus.spec (GF := GF) (hG := hG) := by
  intro c r id s
  wp_start as Hphys
  wp_auto
  wp_apply wp_getBasicStatus c r id s $$ Hphys as %hp ⟨#Hhs, Hphys⟩
  -- `if s.RaftState == StateLeader { s.Progress = getProgressCopy(r) }`
  wp_if_destruct
  all_goals try (
    have _ : stateW64 s.role = W64 2 := Hif
    wp_apply wp_getProgressCopy c c.voters r id s $$ [$Hphys] as %pm ⟨Hpm, Hphys⟩
    ihave Hprog : iprop(⌜pm = null⌝ ∨ progCopyOwn pm) $$ [Hpm]
    · iright; iexact Hpm)
  all_goals try (
    have _ : ¬ stateW64 s.role = W64 2 := Hif
    ihave Hprog : iprop(⌜(zero_val Status).Progress' = null⌝ ∨ progCopyOwn (zero_val Status).Progress')
      $$ []
    · ileft; ipureintro; rfl)
  -- `s.Config = r.trk.Config.Clone()`
  all_goals (
    icases ownRaftPhysC_tracker_same (c := c) (V := c.voters) r id s $$ Hphys with
      ⟨%tv, Htrkf, Htrk, Hback⟩
    iunfold ownTrackerC at Htrk
    iNamed Htrk
    icases (Access.access
      (A := iprop((r.[raft, go!"trk"]).[tracker.ProgressTracker, go!"Config"] ↦ tv.Config'))
      (A' := iprop((r.[raft, go!"trk"]).[tracker.ProgressTracker, go!"Config"] ↦ tv.Config'))
      (P := iprop(r.[raft, go!"trk"] ↦ tv))) $$ Htrkf with ⟨Hf, Hfb⟩
    wp_apply wp_Config_Clone _ _ c _ _ $$ [$Hf $Hcfg] as %cfg' ⟨Hf, Hcfg, Hcfg'⟩
    ihave Htrkf := Hfb $$ Hf
    ihave Hphys := Hback $$ Htrkf [Hvotes Hprogs Hcfg]
    · iunfold ownTrackerC
      iframe Hvotes Hprs Hprogs Hcfg
      ipureintro; exact ⟨Hinv, Hdom, Hflags, Hsize, HmaxInfl⟩
    try wp_auto
    iapply HΦ
    iframe Hphys
    iunfold statusOwnRaw
    iright
    simp only [basicStatusOf]
    isplitr
    · iexists _; iexact Hhs
    isplitl [Hcfg']
    · iexists _; iexact Hcfg'
    icases Hprog with (%Hn | Hp)
    · ileft; ipureintro; first | trivial | exact Hn
    · iright; iExactEq Hp; rfl)

end proof

end EtcdGrove
end Perennial
