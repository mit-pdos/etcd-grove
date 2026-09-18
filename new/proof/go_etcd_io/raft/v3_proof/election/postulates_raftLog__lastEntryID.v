Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_raftLog__lastEntryID.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raftLog__term.

Module Type RAFTLOG__LASTENTRYID_POSTULATES.
  Include RAFTLOG__LASTINDEX.
  Include RAFTLOG__TERM.
End RAFTLOG__LASTENTRYID_POSTULATES.
