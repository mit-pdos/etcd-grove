Require Export New.proof.go_etcd_io.raft.election_proof.spec_stepFollower.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__handleAppendEntries.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__handleHeartbeat.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__send.

(** [stepFollower]'s direct callees: [MsgApp]'s [handleAppendEntries],
    [MsgHeartbeat]'s [handleHeartbeat], and [send] for a forwarded
    [MsgProp].  The other types call nothing but the logger. *)
Module Type STEPFOLLOWER_POSTULATES.
  Include RAFT__HANDLEAPPENDENTRIES.
  Include RAFT__HANDLEHEARTBEAT.
  Include SEND.
End STEPFOLLOWER_POSTULATES.
