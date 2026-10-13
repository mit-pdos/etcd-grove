/-
Port of election_proof/proof_raft__becomePreCandidate.v.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__becomePreCandidate
public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__ResetVotes

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
theorem raft.becomePreCandidate.wp_proof
    (wp_ProgressTracker_ResetVotes : tracker.ProgressTracker.ResetVotes.spec (GF := GF) (hG := hG)) :
    raft.becomePreCandidate.spec (GF := GF) (hG := hG) := by
  intro c r id s Hrole Hcfg
  wp_start as Hphys
  wp_auto
  -- `becomePreCandidate` panics on a leader; by assumption we are not one.
  have Hnl : stateW64 s.role ≠ W64 2 := by
    cases Hro : s.role <;> first
      | exact absurd Hro Hrole
      | (simp only [stateW64, StateFollower, StateCandidate, StatePreCandidate]; decide)
  wp_apply raft.wp_load_stateC $$ Hphys as Hphys
  rw [decide_eq_false Hnl]
  wp_auto
  -- `r.step = stepCandidate`
  wp_apply raft.wp_store_stepC $$ Hphys as Hphys
  -- `r.trk.ResetVotes()`, on the tracker the accessor hands out; put back at the empty
  -- tally
  icases ownRaftPhysC_tracker c _ _ _ $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  wp_apply wp_ProgressTracker_ResetVotes $$ [$Htrkf $Htrk] as %votesRef ⟨Htrkf, Htrk⟩
  ihave Hphys := Hback $$ Htrkf Htrk
  try wp_auto
  -- `r.tick`, `r.lead = None`, `r.state = StatePreCandidate`
  wp_apply raft.wp_store_tickC (Hf := .inl rfl) $$ Hphys as Hphys
  wp_apply raft.wp_store_leadC $$ Hphys as Hphys
  rw [show go_etcd_io.raft.v3.StatePreCandidate = #(stateW64 .preCandidate) from rfl]
  wp_apply raft.wp_store_stateC _ _ _ _ .preCandidate (fun _ => Hcfg) $$ Hphys as Hphys
  wp_apply raft.wp_load_idC $$ Hphys as Hphys
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  wp_raft_logC
  iapply HΦ
  -- the stores give `becomePrecandidate` up to the order of the record updates
  iapply ownRaftPhysC_eq c r id _ (becomePrecandidate s) (by cases s; rfl) $$ Hphys

end proof

end EtcdGrove
end Perennial
