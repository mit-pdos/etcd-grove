Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_raftLog__append.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_unstable__truncateAndAppend.

Module Type RAFTLOG__APPEND_POSTULATES.
  Include RAFTLOG__LASTINDEX.
  Include UNSTABLE__TRUNCATEANDAPPEND.
End RAFTLOG__APPEND_POSTULATES.
