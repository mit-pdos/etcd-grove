Require Export New.proof.go_etcd_io.raft.election_proof.spec_raftLog__isUpToDate.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__lastEntryID.

Module Type RAFTLOG__ISUPTODATE_POSTULATES.
  Include RAFTLOG__LASTENTRYID.
End RAFTLOG__ISUPTODATE_POSTULATES.
