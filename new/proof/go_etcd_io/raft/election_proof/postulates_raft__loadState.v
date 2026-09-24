Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__loadState.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__lastIndex.

Module Type RAFT__LOADSTATE_POSTULATES.
  Include RAFTLOG__LASTINDEX.
End RAFT__LOADSTATE_POSTULATES.
