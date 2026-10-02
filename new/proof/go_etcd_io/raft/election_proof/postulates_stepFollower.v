Require Export New.proof.go_etcd_io.raft.election_proof.spec_stepFollower.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__handleAppendEntries.

(** [stepFollower]'s direct callees on the paths specified: [MsgApp]'s
    [handleAppendEntries].  [MsgVoteResp] and the leaderless [MsgProp]
    call nothing but the logger.  ([send], for the forwarding arm, joins
    when that arm is proved; [handleHeartbeat] with [MsgHeartbeat].) *)
Module Type STEPFOLLOWER_POSTULATES.
  Include RAFT__HANDLEAPPENDENTRIES.
End STEPFOLLOWER_POSTULATES.
