Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_stepFollower_MsgVoteResp.

(** No direct callees.  On the [MsgVoteResp] path [stepFollower] calls
    nothing: every [send]/[handleX]/[hup]/[Logger] call in its body sits
    inside a type-switch arm that a [MsgVoteResp] does not enter. *)
Module Type STEPFOLLOWER_POSTULATES.
End STEPFOLLOWER_POSTULATES.
