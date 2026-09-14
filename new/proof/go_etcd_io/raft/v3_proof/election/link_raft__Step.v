(** * Link: [raft.raft__Step]

    [raft__Step] is proved, so this file carries no [Axiom]. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__Step.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__Step_MsgHup.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__Step_MsgVote.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__Step_MsgVoteResp.

Module StepPostulates : STEP_POSTULATES.
  Include StepMsgHup.
  Include StepMsgVote.
  Include StepMsgVoteResp.
End StepPostulates.

Module Step := StepProof StepPostulates.

(** Implicits are not inferred through a folded [_body], and an [Arguments]
    inside the [Module Type] does not survive functor application. *)
Arguments Step.wp_raft__Step {_ _ _ _ _ _ _ _}.
