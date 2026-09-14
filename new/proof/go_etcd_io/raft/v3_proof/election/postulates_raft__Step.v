(** * Postulates: [raft.Step]

    The direct callees of [Step] and of its three internal branches.  Only
    *direct* callees: a transitive include would re-declare a label another
    branch already contributes, and [Include] rejects that. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_raft__Step.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__hup.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__becomeFollower.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_voteRespMsgType.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__send_vote.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_stepCandidate_MsgVoteResp.

Module Type STEP_POSTULATES.
  Include HUP.
  Include BECOMEFOLLOWER.
  Include VOTERESPMSGTYPE.
  Include SEND_VOTE.
  Include STEPCANDIDATE.
End STEP_POSTULATES.
