/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_prevote_lemmas.v.

Pure lemmas shared by `Step`'s pre-vote branches (`proof_raft__Step_MsgPreVote*.v`,
`proof_raft__Step_MsgPreVoteResp*.v`), 2026-10-04.

Proof structure, not specification: no `Module Type`, no `Parameter`, no Hoare triple.
Each lemma takes a `stepX` result relation apart for `MsgPreVoteResp`, outside any WP,
where the `decide` chains are cheap. Only files in this directory may `Require` it.

Lean notes: Rocq's section variable `cfg` is an explicit first argument of every lemma
that uses it. Rocq's `case_decide … w32_ne` chains are the local macro `mtype_simp`
(unfold the message-type constants, decide the equalities between them).
-/
import EtcdGrove.Raft.ElectionProof.Proof.raft__Step.Base

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section prevote
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

namespace StepProof

/-- Unfold the message-type constants and decide the equalities between them (the
`case_decide … w32_ne` chains of the Rocq proofs). -/
local macro "mtype_simp" : tactic =>
  `(tactic| simp (config := { decide := true }) only [Perennial.EtcdGrove.MsgBeat,
      Perennial.EtcdGrove.MsgHup, Perennial.EtcdGrove.MsgProp, Perennial.EtcdGrove.MsgApp,
      Perennial.EtcdGrove.MsgAppResp, Perennial.EtcdGrove.MsgVote,
      Perennial.EtcdGrove.MsgVoteResp, Perennial.EtcdGrove.MsgSnap,
      Perennial.EtcdGrove.MsgHeartbeat, Perennial.EtcdGrove.MsgHeartbeatResp,
      Perennial.EtcdGrove.MsgPreVote, Perennial.EtcdGrove.MsgPreVoteResp,
      or_false, false_or, false_and, and_false, ↓reduceIte, Bool.false_eq_true] at *)

/-- `stepFollower` has no `MsgPreVoteResp` arm. -/
theorem followerStepResult_prevoteresp (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (dropped : Bool) (s' : NState) :
    m.Type' = MsgPreVoteResp →
    FollowerStepResult id s m ents sv dropped s' → dropped = false ∧ s' = s := by
  intro Hty H
  unfold FollowerStepResult at H
  rw [Hty] at H
  mtype_simp
  exact H

/-- `stepLeader` has none either. -/
theorem leaderStepResult_prevoteresp (cfg : GSet w64) (id : w64) (s : NState)
    (m : raftpb.Message) (ents : List raftpb.Entry) (dropped : Bool) (s' : NState) :
    m.Type' = MsgPreVoteResp →
    LeaderStepResult cfg id s m ents dropped s' → dropped = false ∧ s' = s := by
  intro Hty H
  unfold LeaderStepResult at H
  rw [Hty] at H
  mtype_simp
  obtain ⟨rfl, Hres⟩ := H
  refine ⟨rfl, ?_⟩
  unfold LeaderNonpropResult at Hres
  rw [Hty] at Hres
  rcases Hres with ⟨-, Hres⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩ | ⟨Hc, -⟩
  · exact Hres
  all_goals exact absurd Hc (by w32_ne)

/-- `stepCandidate` on a `MsgPreVoteResp`: nothing at a candidate; at a pre-candidate,
the tally and then win / lose / wait, which is `step_prevoteRespResult`. -/
theorem candidateStepResult_prevoteresp (cfg : GSet w64) (id : w64) (s : NState)
    (m : raftpb.Message) (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (dropped : Bool)
    (s' : NState) :
    m.Type' = MsgPreVoteResp →
    (s.role = .candidate ∨ s.role = .preCandidate) →
    id ∈ cfg →
    uint.Z s.term + 1 < 2 ^ 64 →
    NStateWf s →
    CandidateStepResult cfg id s m ents sv dropped s' →
    dropped = false ∧ NStateWf s' ∧ Step cfg id (toPState s) [] (toPState s') := by
  intro Hty Hrole Hin Hnw Hwf H
  unfold CandidateStepResult at H
  rw [Hty] at H
  mtype_simp
  obtain ⟨rfl, Hres⟩ := H
  refine ⟨rfl, ?_⟩
  by_cases Hp : s.role = .preCandidate
  · simp only [Hp, ↓reduceIte] at Hres
    obtain ⟨won, lost, peers, pvs, Hw, -, rfl⟩ := Hres
    refine ⟨nstateWf_prvals _ _ (nstateWf_prevoteRespResult _ _ _ _ _ _ _ Hwf), ?_⟩
    exact step_prevoteRespResult cfg id s _ _ won lost peers pvs Hp Hin Hnw
      (fun Hwon => (Hw Hwon).2)
  · simp only [Hp, ↓reduceIte] at Hres
    subst Hres
    exact ⟨Hwf, .refl _⟩

end StepProof

end prevote

end EtcdGrove
end Perennial
