(** * Link: [raft.raft__Step_MsgVote]

    [raft__Step_MsgVote] is in scope but unfinished: the hole is the [Admitted] in
    [proof_raft__Step_MsgVote.v], not an [Axiom] here. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__Step_MsgVote.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__becomeFollower.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_voteRespMsgType.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__send_vote.

Module StepMsgVotePostulates : STEP_MSGVOTE_POSTULATES.
  Include BecomeFollower.
  Include VoteRespMsgType.
  Include SendVote.
End StepMsgVotePostulates.

Module StepMsgVote := StepMsgVoteProof StepMsgVotePostulates.

(** Implicits are not inferred through a folded [_body], and an [Arguments]
    inside the [Module Type] does not survive functor application. *)
Arguments StepMsgVote.wp_raft__Step_MsgVote {_ _ _ _ _ _ _ _}.
