Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_MajorityConfig__VoteResult.

(** [MajorityConfig.VoteResult] calls no other Go function: the loop body is
    a map lookup and two increments, and [len] is a builtin. *)
Module Type MAJORITYCONFIG__VOTERESULT_POSTULATES.
End MAJORITYCONFIG__VOTERESULT_POSTULATES.
