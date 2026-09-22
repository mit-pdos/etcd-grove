Require Export New.proof.go_etcd_io.raft.election_proof.spec_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_unstable__maybeLastIndex.

Module Type RAFTLOG__LASTINDEX_POSTULATES.
  Include UNSTABLE__MAYBELASTINDEX.
End RAFTLOG__LASTINDEX_POSTULATES.
