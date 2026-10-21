/- (D22 S-d2, 2026-10-21) Lean-first. -/
module

public import Spec.go_etcd_io.raft.v3.raft__appliedSnap
public import Spec.go_etcd_io.raft.v3.raft__appliedTo
public import Spec.go_etcd_io.raft.v3.raftLog__stableSnapTo
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex

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

/-- The index through the getters; `stableSnapTo` on the log in the windows, then `appliedTo`,
whose premises the log gives: the snapshot at or below the boundary, which is at most `committed`
and below `offsetInProgress` (`ownRaftLogW_struct`), and on a hit the boundary itself (the pending
snapshot is `prev`, `ownRaftLogW_snap_prev`), so `appliedSnap`'s window ends there. -/
theorem raft.appliedSnap.wp_proof
    (wp_raftLog_stableSnapTo : raftLog.stableSnapTo.spec (GF := GF) (hG := hG))
    (wp_raft_appliedTo : raft.appliedTo.spec (GF := GF) (hG := hG))
    (wp_Snapshot_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_SnapshotMetadata_GetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG)) :
    raft.appliedSnap.spec (GF := GF) (hG := hG) := by
  intro c r id s sp dq sv Hiff Haps Hle Hal Hun Hns Hsx Hkx
  wp_start as H
  iNamed H
  wp_auto
  wp_apply wp_Snapshot_GetMetadata.1 sp dq sv $$ [$Hsnap] as %pm ⟨Hm, Hback⟩
  wp_apply wp_SnapshotMetadata_GetIndex pm dq _ $$ [$Hm] as Hm
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
  ihave Hphys := Hlogback $$ %_ Hlog %(LogGhOk.of_off Hun Hkeep (SnpOk.stableSnap _ Hgh0.1.2) Hst1)
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
  wp_apply wp_raft_appliedTo c r id { s with logst := logStableSnap s.logst sv.Metadata'.Index' }
      sv.Metadata'.Index' (W64 0) (by simp only; omega) (fun _ => by simp only; omega) Hal Hsa1 Haps1
      Hsx1 (fun _ k hk => Hkx k hk) $$ [$Hphys] as Hphys
  iapply HΦ
  iframe Hback Hphys

end proof

end EtcdGrove
end Perennial
