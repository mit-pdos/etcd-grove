Require Export New.proof.go_etcd_io.raft.election_proof.spec_raftLog__lastEntryID.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__term.

Module Type RAFTLOG__LASTENTRYID_POSTULATES.
  Include RAFTLOG__LASTINDEX.
  Include RAFTLOG__TERM.
End RAFTLOG__LASTENTRYID_POSTULATES.
