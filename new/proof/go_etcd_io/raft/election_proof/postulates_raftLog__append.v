Require Export New.proof.go_etcd_io.raft.election_proof.spec_raftLog__append.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_unstable__truncateAndAppend.

Module Type RAFTLOG__APPEND_POSTULATES.
  Include RAFTLOG__LASTINDEX.
  Include UNSTABLE__TRUNCATEANDAPPEND.
End RAFTLOG__APPEND_POSTULATES.
