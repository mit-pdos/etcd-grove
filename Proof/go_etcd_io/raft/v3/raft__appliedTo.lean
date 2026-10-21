/-
Port of election_proof/proof_raft__appliedTo.v (857d09190).

Lean notes: Rocq's `wp_max2_uint64` is stepped by hand (`wp_func_call`, `wp_call`,
`wp_if_destruct`, as in `Proof/raftLog__appliedTo.lean`); each branch calls
`raftLog.appliedTo` at the value it computed, and the final state is matched to
`logAppliedTo` (`w64Max`) with `ownRaftPhys_eq`.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__appliedTo
public import Spec.go_etcd_io.raft.v3.raftLog__appliedTo

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

theorem raft.appliedTo.wp_proof
    (wp_raftLog_appliedTo : raftLog.appliedTo.spec (GF := GF) (hG := hG)) :
    raft.appliedTo.spec (GF := GF) (hG := hG) := by
  intro c r id s index size Hidx Hipo Hal0 Hsa Hapsb Hsx Hkx
  wp_start as Hphys
  iNamed Hphys
  wp_auto
  -- `oldApplied := r.raftLog.applied` (D22 S-d2: the struct in the windows)
  wp_apply raft.wp_load_raftLogCW $$ Hphys as Hphys
  icases ownRaftPhysCVW_log_at c r id s $$ Hphys with ⟨Hlog, %Hgh0, Hback⟩
  icases ownRaftLogW_struct _ _ $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
  obtain ⟨Hap, Hapl, Hapc, -, -⟩ := Hlv
  wp_auto
  ihave Hlog := Hlb $$ Hl
  ihave Hphys := Hback $$ %s.logst Hlog %Hgh0 %(fun _ => Int.le_refl _)
  ihave Hphys := ownRaftPhysCVW_eq c r id _ s (by cases s; rfl) $$ Hphys
  rw [Hap]
  -- `max(index, oldApplied)`, as `w64Max`
  wp_func_call
  wp_call
  wp_if_destruct
  all_goals
    -- `r.raftLog.appliedTo(newApplied, size)`: the window ends, the struct is quiet again
    wp_apply raft.wp_load_raftLogCW $$ Hphys as Hphys
    icases ownRaftPhysCVW_log_atQ c r id s $$ Hphys with ⟨Hlog, %Hgh0, Hback⟩
    first
      | wp_apply wp_raftLog_appliedTo _ _ index size (by omega) Hipo Hsx $$ [$Hlog] as Hlog
      | wp_apply wp_raftLog_appliedTo _ _ s.logst.applied size (by omega)
          (fun h => absurd Hapl (Int.not_le.2 h)) (fun _ _ h => absurd Hapl (Int.not_le.2 h))
          $$ [$Hlog] as Hlog
    ihave Hlog := ownRaftLogW_quietW _ _ $$ Hlog %(⟨Hsa, by
      cases h : s.logst.aps
      · rfl
      · have := Hapsb h
        simp only [Bool.true_and, decide_eq_false_iff_not]
        omega⟩)
    ihave Hphys := Hback $$ %_ Hlog %(LogGhOk.of_fields Hgh0 rfl rfl rfl rfl rfl
        (hx := fun h => SnpExt.raise h rfl rfl rfl (by simp only; rw [w64Max_spec]; omega)
          (fun ha k hk => by
            have := Hkx ha k hk
            simp only; rw [w64Max_spec]
            first | omega | (simp only [decide_eq_true_eq, decide_eq_false_iff_not] at *; omega))))
      %(fun _ => logLast_le_of_fields rfl rfl rfl)
    -- `r.trk.Config.AutoLeave`: off, or the node is no leader (`Hal0`) -- the rest is dead
    icases ownRaftPhysC_tracker_same c r id _ $$ Hphys with ⟨%tv, Htrkf, Htrk, Htback⟩
    icases ownTrackerC_autoleave c _ _ $$ Htrk with ⟨%Hal, Htrk⟩
    wp_auto
    rw [Hal]
    ihave Hphys := Htback $$ %tv Htrkf Htrk
    cases Hcal : c.autoLeave
    · wp_auto
      iapply HΦ
      iapply ownRaftPhysC_eq c _ _ _ _ ?_ $$ Hphys
      simp only [logAppliedTo, w64Max]
      split <;> first | rfl | omega
    · have Hnl : s.role ≠ .leader := Hal0 Hcal
      wp_auto
      wp_apply raft.wp_load_pendingConfIndexC $$ Hphys as Hphys
      wp_if_destruct
      · wp_apply raft.wp_load_stateC $$ Hphys as Hphys
        have Hst : stateW64 s.role ≠ W64 2 := by
          cases h : s.role <;> simp_all [stateW64] <;> decide
        try wp_auto
        rw [decide_eq_false (show ¬ (stateW64 s.role = W64 2) from Hst)]
        try wp_auto
        iapply HΦ
        iapply ownRaftPhysC_eq c _ _ _ _ ?_ $$ Hphys
        simp only [logAppliedTo, w64Max]
        split <;> first | rfl | omega
      · try wp_auto
        iapply HΦ
        iapply ownRaftPhysC_eq c _ _ _ _ ?_ $$ Hphys
        simp only [logAppliedTo, w64Max]
        split <;> first | rfl | omega

end proof

end EtcdGrove
end Perennial
