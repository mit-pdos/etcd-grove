(** * Link: [raft.raft__Step_MsgVoteResp]

    [raft__Step_MsgVoteResp] is in scope but unfinished: the hole is the [Admitted] in
    [proof_raft__Step_MsgVoteResp.v], not an [Axiom] here. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__Step_MsgVoteResp.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_stepCandidate_MsgVoteResp.

Module StepMsgVoteRespPostulates : STEP_MSGVOTERESP_POSTULATES.
  Include StepCandidate.
End StepMsgVoteRespPostulates.

Module StepMsgVoteResp := StepMsgVoteRespProof StepMsgVoteRespPostulates.

(** Implicits are not inferred through a folded [_body], and an [Arguments]
    inside the [Module Type] does not survive functor application. *)
Arguments StepMsgVoteResp.wp_raft__Step_MsgVoteResp {_ _ _ _ _ _ _ _}.
