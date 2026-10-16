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
  intro c r id s index size Hidx Hal0
  wp_start as Hphys
  iNamed Hphys
  wp_auto
  -- `oldApplied := r.raftLog.applied`
  wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
  icases ownRaftPhysC_log_same c r id s $$ Hphys with ⟨Hlog, Hback⟩
  icases ownRaftLog_committed _ _ $$ Hlog with ⟨%Hcb, Hlog⟩
  icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
  obtain ⟨Hcm, Hap⟩ := Hlv
  wp_auto
  ihave Hlog := Hlb $$ Hl
  ihave Hphys := Hback $$ Hlog
  rw [Hap]
  -- `max(index, oldApplied)`, as `w64Max`
  wp_func_call
  wp_call
  wp_if_destruct
  all_goals
    -- `r.raftLog.appliedTo(newApplied, size)`
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_at c r id s $$ Hphys with ⟨Hlog, %Hgh0, Hback⟩
    first
      | wp_apply wp_raftLog_appliedTo _ _ index size (by omega) $$ [$Hlog] as Hlog
      | wp_apply wp_raftLog_appliedTo _ _ s.logst.applied size (by omega) $$ [$Hlog] as Hlog
    ihave Hphys := Hback $$ %_ Hlog %(LogGhOk.of_fields Hgh0 rfl rfl rfl rfl rfl)
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
        rw [decide_eq_false (by simpa [StateLeader] using Hst)]
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
