Require Export New.proof.go_etcd_io.raft.election_proof.spec_raftLog__firstIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_unstable__maybeFirstIndex.

Module Type RAFTLOG__FIRSTINDEX_POSTULATES.
  Include UNSTABLE__MAYBEFIRSTINDEX.
End RAFTLOG__FIRSTINDEX_POSTULATES.
