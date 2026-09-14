(** * Postulates: [raft.raft__Step_MsgVoteResp]

    Only *direct* callees.  Never include another [_POSTULATES]: a transitive
    include re-declares a label some other branch already contributes, and
    [Include] rejects that. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_raft__Step_MsgVoteResp.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_stepCandidate_MsgVoteResp.

Module Type STEP_MSGVOTERESP_POSTULATES.
  Include STEPCANDIDATE.
End STEP_MSGVOTERESP_POSTULATES.
