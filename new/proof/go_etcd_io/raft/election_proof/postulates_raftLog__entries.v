Require Export New.proof.go_etcd_io.raft.election_proof.spec_raftLog__entries.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__slice.

Module Type RAFTLOG__ENTRIES_POSTULATES.
  Include RAFTLOG__LASTINDEX.
  Include RAFTLOG__SLICE.
End RAFTLOG__ENTRIES_POSTULATES.
