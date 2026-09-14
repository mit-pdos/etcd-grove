(** * Postulates: [raft.raft__Step]

    Only *direct* callees.  Never include another [_POSTULATES]: a transitive
    include re-declares a label some other branch already contributes, and
    [Include] rejects that. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_raft__Step.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__Step_MsgHup.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__Step_MsgVote.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__Step_MsgVoteResp.

Module Type STEP_POSTULATES.
  Include STEP_MSGHUP.
  Include STEP_MSGVOTE.
  Include STEP_MSGVOTERESP.
End STEP_POSTULATES.
