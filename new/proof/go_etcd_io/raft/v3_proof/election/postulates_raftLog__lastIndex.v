Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_unstable__maybeLastIndex.

Module Type RAFTLOG__LASTINDEX_POSTULATES.
  Include UNSTABLE__MAYBELASTINDEX.
End RAFTLOG__LASTINDEX_POSTULATES.
