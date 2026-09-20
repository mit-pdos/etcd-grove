Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_raft__hasUnappliedConfChanges.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raftLog__scan.

Module Type RAFT__HASUNAPPLIEDCONFCHANGES_POSTULATES.
  Include RAFTLOG__SCAN.
End RAFT__HASUNAPPLIEDCONFCHANGES_POSTULATES.
