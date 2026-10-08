/-
Port of `election_proof/proof_raft__becomeCandidate.v`.
-/
import EtcdGrove.Raft.Spec.raft__becomeCandidate
import EtcdGrove.Raft.Spec.raft__reset
import EtcdGrove.Raft.Spec.traceBecomeCandidate

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

theorem raft.becomeCandidate.wp_proof
    (wp_raft_reset : raft.reset.spec (GF := GF) (hG := hG))
    (wp_traceBecomeCandidate : traceBecomeCandidate.spec (GF := GF) (hG := hG)) :
    raft.becomeCandidate.spec (GF := GF) (hG := hG) := by
  intro cfg r id s Hrole
  wp_start as Hphys
  wp_alloc r_ptr as r; wp_pures; wp_load; wp_pures
  -- `becomeCandidate` panics on a leader; by assumption we are not one.
  have Hnl : stateW64 s.role ≠ W64 2 := by
    cases h : s.role <;> simp_all [stateW64] <;> decide
  wp_apply raft.wp_load_state $$ Hphys as Hphys
  wp_pures
  wp_if_destruct
  · exact absurd Hif Hnl
  wp_load; wp_pures
  -- `r.step := stepCandidate`, then `reset` at `r.Term + 1`
  wp_apply raft.wp_store_step $$ Hphys as Hphys
  wp_pures; wp_load; wp_pures
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  wp_pures; wp_load; wp_pures
  -- `reset`'s state is left to the frame (in Rocq, giving it explicitly ran for 24
  -- minutes before failing, 2026-09-22)
  wp_apply wp_raft_reset $$ [$Hphys] as %pvs ⟨Hphys, -⟩
  wp_pures; wp_load; wp_pures; wp_load; wp_pures
  -- `Match` is irrelevant for a non-leader (`toPState`)
  -- `r.tick`, `r.Vote := r.id`, `r.state := StateCandidate`
  wp_apply raft.wp_store_tick $$ Hphys as Hphys
  wp_pures; wp_load; wp_pures
  wp_apply raft.wp_load_id $$ Hphys as Hphys
  wp_pures; wp_load; wp_pures
  wp_apply raft.wp_store_Vote $$ Hphys as Hphys
  wp_pures; wp_load; wp_pures
  rw [show (go_etcd_io.raft.v3.StateCandidate : val) = #(stateW64 .candidate) from rfl]
  wp_apply raft.wp_store_state (ro := .candidate) $$ Hphys as Hphys
  wp_pures; wp_load; wp_pures
  wp_apply raft.wp_load_id $$ Hphys as Hphys
  wp_pures; wp_load; wp_pures
  wp_apply raft.wp_load_Term $$ Hphys as Hphys
  wp_pures
  wp_raft_log
  wp_pures; wp_load; wp_pures; iclear r
  wp_apply wp_traceBecomeCandidate
  wp_pures
  iapply HΦ $$ %pvs
  -- the stores above give `becomeCandidate` up to the order of the record updates
  iapply ownRaftPhys_eq $$ Hphys
  cases s; rfl

end proof

end EtcdGrove
end Perennial
