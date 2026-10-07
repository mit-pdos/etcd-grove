/- Port of election_proof/proof_raft__Step_helpers/proof_raft__Step_prevote_lemmas.v.

Pure lemmas shared by `Step`'s pre-vote branches (`proof_raft__Step_MsgPreVote*.v`,
`proof_raft__Step_MsgPreVoteResp*.v`), 2026-10-04.

Proof structure, not specification: no `Module Type`, no `Parameter`, no Hoare triple.
Each lemma takes a `stepX` result relation apart for `MsgPreVoteResp`, outside any WP,
where the `decide` chains are cheap. Only files in this directory may `Require` it.

Lean notes: Rocq's section variable `cfg` is an explicit first argument of every lemma
that uses it.
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

/-- `stepFollower` has no `MsgPreVoteResp` arm. -/
theorem followerStepResult_prevoteresp (id : w64) (s : NState) (m : raftpb.Message)
    (ents : List raftpb.Entry) (sv : raftpb.Snapshot) (dropped : Bool) (s' : NState) :
    m.Type' = MsgPreVoteResp →
    FollowerStepResult id s m ents sv dropped s' → dropped = false ∧ s' = s := by
  -- PORT: proof
  sorry

/-- `stepLeader` has none either. -/
theorem leaderStepResult_prevoteresp (cfg : GSet w64) (id : w64) (s : NState)
    (m : raftpb.Message) (ents : List raftpb.Entry) (dropped : Bool) (s' : NState) :
    m.Type' = MsgPreVoteResp →
    LeaderStepResult cfg id s m ents dropped s' → dropped = false ∧ s' = s := by
  -- PORT: proof
  sorry

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
  -- PORT: proof
  sorry

end StepProof

end prevote

end EtcdGrove
end Perennial
