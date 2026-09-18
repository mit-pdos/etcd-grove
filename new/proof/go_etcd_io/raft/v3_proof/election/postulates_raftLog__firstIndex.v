Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_raftLog__firstIndex.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_unstable__maybeFirstIndex.

Module Type RAFTLOG__FIRSTINDEX_POSTULATES.
  Include UNSTABLE__MAYBEFIRSTINDEX.
End RAFTLOG__FIRSTINDEX_POSTULATES.
