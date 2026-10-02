Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__handleSnapshot.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__restore.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__send.

(** [handleSnapshot]'s callees: [restore], [lastIndex] (for the reply after
    a restore; already a postulate of [restore]'s) and [send]. *)
Module Type RAFT__HANDLESNAPSHOT_POSTULATES.
  Include RAFT__RESTORE.
  Include RAFTLOG__LASTINDEX.
  Include SEND.
End RAFT__HANDLESNAPSHOT_POSTULATES.
