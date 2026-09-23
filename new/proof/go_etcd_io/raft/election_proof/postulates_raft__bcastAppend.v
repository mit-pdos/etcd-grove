Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__bcastAppend.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_ProgressTracker__Visit.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__sendAppend.

Module Type RAFT__BCASTAPPEND_POSTULATES.
  Include PROGRESSTRACKER__VISIT.
  Include RAFT__SENDAPPEND.
End RAFT__BCASTAPPEND_POSTULATES.
