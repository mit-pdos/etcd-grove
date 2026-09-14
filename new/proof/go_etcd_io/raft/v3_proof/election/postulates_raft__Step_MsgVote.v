(** * Postulates: [raft.raft__Step_MsgVote]

    Only *direct* callees.  Never include another [_POSTULATES]: a transitive
    include re-declares a label some other branch already contributes, and
    [Include] rejects that. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_raft__Step_MsgVote.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__becomeFollower.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_voteRespMsgType.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__send_vote.

Module Type STEP_MSGVOTE_POSTULATES.
  Include BECOMEFOLLOWER.
  Include VOTERESPMSGTYPE.
  Include SEND_VOTE.
End STEP_MSGVOTE_POSTULATES.
