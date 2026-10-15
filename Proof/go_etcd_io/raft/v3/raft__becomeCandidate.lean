/-
Port of `election_proof/proof_raft__becomeCandidate.v`.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__becomeCandidate
public import Spec.go_etcd_io.raft.v3.raft__reset
public import Spec.go_etcd_io.raft.v3.traceBecomeCandidate

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

theorem raft.becomeCandidate.wp_proof
    (wp_raft_reset : raft.reset.spec (GF := GF) (hG := hG))
    (wp_traceBecomeCandidate : traceBecomeCandidate.spec (GF := GF) (hG := hG)) :
    raft.becomeCandidate.spec (GF := GF) (hG := hG) := by
  intro c r id s Hrole Hnw Hcfg
  wp_start as Hphys
  wp_auto
  -- `becomeCandidate` panics on a leader; by assumption we are not one.
  have Hnl : stateW64 s.role ≠ W64 2 := by
    cases h : s.role <;> simp_all [stateW64] <;> decide
  wp_apply raft.wp_load_stateC $$ Hphys as Hphys
  wp_if_destruct
  · exact absurd Hif Hnl
  -- `r.step := stepCandidate`, then `reset` at `r.Term + 1`
  wp_apply raft.wp_store_stepC $$ Hphys as Hphys
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  -- `reset`'s state is left to the frame (in Rocq, giving it explicitly ran for 24
  -- minutes before failing, 2026-09-22)
  wp_apply wp_raft_reset c r id { s with stepfn := functions stepCandidate [] }
    (s.term + W64 1) (by word) $$ [$Hphys] as %pvs ⟨Hphys, -⟩
  -- `Match` is irrelevant for a non-leader (`toPState`)
  -- `r.tick`, `r.Vote := r.id`, `r.state := StateCandidate`
  wp_apply raft.wp_store_tickC (Hf := .inl rfl) $$ Hphys as Hphys
  wp_apply raft.wp_load_idC $$ Hphys as Hphys
  wp_apply raft.wp_store_VoteC $$ Hphys as Hphys
  rw [show (go_etcd_io.raft.v3.StateCandidate : val) = #(stateW64 .candidate) from rfl]
  wp_apply raft.wp_store_stateC (ro := .candidate) (Hro := fun _ => Hcfg) $$ Hphys as Hphys
  wp_apply raft.wp_load_idC $$ Hphys as Hphys
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  wp_raft_logC
  wp_apply wp_traceBecomeCandidate
  iapply HΦ $$ %pvs
  -- the stores above give `becomeCandidate` up to the order of the record updates
  iapply ownRaftPhysC_eq $$ Hphys
  cases s; rfl

end proof

end EtcdGrove
end Perennial
