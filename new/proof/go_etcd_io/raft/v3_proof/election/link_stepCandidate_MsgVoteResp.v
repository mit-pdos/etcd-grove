(** * Link: [raft.stepCandidate_MsgVoteResp]

    [stepCandidate_MsgVoteResp] is in scope but unfinished: the hole is the [Admitted] in
    [proof_stepCandidate_MsgVoteResp.v], not an [Axiom] here. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_stepCandidate_MsgVoteResp.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__poll.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__becomeLeader.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__send_vote.

Module StepCandidatePostulates : STEPCANDIDATE_POSTULATES.
  Include Poll.
  Include BecomeLeader.
  Include SendVote.
End StepCandidatePostulates.

Module StepCandidate := StepCandidateProof StepCandidatePostulates.

(** Implicits are not inferred through a folded [_body], and an [Arguments]
    inside the [Module Type] does not survive functor application. *)
Arguments StepCandidate.wp_stepCandidate_MsgVoteResp {_ _ _ _ _ _ _ _}.
