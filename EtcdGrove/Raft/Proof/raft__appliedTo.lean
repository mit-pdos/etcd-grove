/-
Port of election_proof/proof_raft__appliedTo.v (857d09190).

Lean notes: Rocq's `wp_max2_uint64` is stepped by hand (`wp_func_call`, `wp_call`,
`wp_if_destruct`, as in `Proof/raftLog__appliedTo.lean`); each branch calls
`raftLog.appliedTo` at the value it computed, and the final state is matched to
`logAppliedTo` (`w64Max`) with `ownRaftPhys_eq`.
-/
import EtcdGrove.Raft.Spec.raft__appliedTo
import EtcdGrove.Raft.Spec.raftLog__appliedTo

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

theorem raft.appliedTo.wp_proof
    (wp_raftLog_appliedTo : raftLog.appliedTo.spec (GF := GF) (hG := hG)) :
    raft.appliedTo.spec (GF := GF) (hG := hG) := by
  intro cfg r id s index size Hidx
  wp_start as Hphys
  iNamed Hphys
  wp_alloc r_ptr as r; wp_pures; wp_alloc size_ptr as size; wp_pures; wp_alloc index_ptr as index
  wp_pures; wp_load; wp_pures
  -- `oldApplied := r.raftLog.applied`
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  wp_pures
  icases ownRaftPhys_log_same cfg r id s $$ Hphys with ⟨Hlog, Hback⟩
  icases ownRaftLog_committed _ _ $$ Hlog with ⟨%Hcb, Hlog⟩
  icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
  obtain ⟨Hcm, Hap⟩ := Hlv
  wp_load; wp_pures; wp_alloc oldApplied_ptr as oldApplied; wp_pures; wp_store; wp_pures; wp_load
  wp_pures; wp_load; wp_pures; iclear index oldApplied
  ihave Hlog := Hlb $$ Hl
  ihave Hphys := Hback $$ Hlog
  rw [Hap]
  -- `max(index, oldApplied)`, as `w64Max`
  wp_func_call
  wp_call
  wp_if_destruct
  all_goals
    wp_alloc newApplied_ptr as newApplied; wp_pures; wp_store; wp_pures; wp_load; wp_pures; wp_load
    wp_pures; wp_load; wp_pures; iclear size
    -- `r.raftLog.appliedTo(newApplied, size)`
    wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
    wp_pures
    icases ownRaftPhys_log_at cfg r id s $$ Hphys with ⟨Hlog, Hback⟩
    first
      | wp_apply wp_raftLog_appliedTo _ _ index size (by omega) $$ [$Hlog] as Hlog
      | wp_apply wp_raftLog_appliedTo _ _ s.logst.applied size (by omega) $$ [$Hlog] as Hlog
    wp_pures; wp_load; wp_pures
    ihave Hphys := Hback $$ %_ Hlog
    -- `r.trk.Config.AutoLeave` is `false`: the rest is dead
    icases ownRaftPhys_tracker_same cfg r id _ $$ Hphys with ⟨%tv, Htrkf, Htrk, Htback⟩
    icases ownTracker_autoleave cfg _ _ $$ Htrk with ⟨%Hal, Htrk⟩
    wp_load
    rw [Hal]
    wp_pures; iclear r newApplied
    ihave Hphys := Htback $$ %tv Htrkf Htrk
    iapply HΦ
    iapply ownRaftPhys_eq _ _ _ _ _ ?_ $$ Hphys
    simp only [logAppliedTo, w64Max]
    split <;> first | rfl | omega

end proof

end EtcdGrove
end Perennial
