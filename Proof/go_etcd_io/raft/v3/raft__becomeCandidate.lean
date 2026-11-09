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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raft.becomeCandidate.wp_proof
    (wp_raft_reset : raft.reset.spec (GF := GF) (hG := hG))
    (wp_traceBecomeCandidate : traceBecomeCandidate.spec (GF := GF) (hG := hG)) :
    raft.becomeCandidate.spec (GF := GF) (hG := hG) := by
  intro c r id s Q Hrole Hnw Hcfg
  wp_start as ⟨Hphys, Hgate⟩
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
  have Htnz : s.term + W64 1 ≠ W64 0 := by word
  wp_apply raft.wp_store_stateC (ro := .candidate) (Hro := fun _ _ => Hcfg)
    (Hrt := fun _ => Htnz) $$ Hphys as Hphys
  wp_apply raft.wp_load_idC $$ Hphys as Hphys
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  wp_raft_logC
  -- (Q8 stage 1, slice 3) the `BecomeCandidate` line, either mode
  -- the stores above give `becomeCandidate` up to the order of the record updates
  ihave Hphys : ownRaftPhysCV c c.voters r id { becomeCandidate id s with prvals := pvs } $$ [Hphys]
  · iapply ownRaftPhysC_eq $$ Hphys
    cases s; rfl
  have Hgh : ({ becomeCandidate id s with prvals := pvs } : NState).gh.tr = s.gh.tr := by
    first | rfl | (simp [becomeCandidate, resetTo, resetTo0]) | (cases s; rfl)
  icases trOwn_split s.gh.tr _ $$ Hphys with ⟨Hown, Hback⟩
  iunfold HookGate at Hgate
  imod Hgate with ⟨%tl, #Htl, Hfire⟩
  wp_apply wp_traceBecomeCandidate c r id { becomeCandidate id s with prvals := pvs } tl Q
    $$ [Htl Hown Hfire] as ⟨Hown, HQ⟩
  · rw [Hgh]
    iframe Htl Hown
    iapply traceFire_mono_E _ tl _ _ _ (fun e he => by rw [nodeEvOf_prvals] at he; exact he) $$ Hfire
  rw [Hgh]
  ihave Hphys := Hback $$ Hown
  iapply HΦ $$ %pvs
  iframe HQ Hphys

end proof

end EtcdGrove
end Perennial
