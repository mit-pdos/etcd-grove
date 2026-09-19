Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_raftLog__isUpToDate.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raftLog__lastEntryID.

Module Type RAFTLOG__ISUPTODATE_POSTULATES.
  Include RAFTLOG__LASTENTRYID.
End RAFTLOG__ISUPTODATE_POSTULATES.
