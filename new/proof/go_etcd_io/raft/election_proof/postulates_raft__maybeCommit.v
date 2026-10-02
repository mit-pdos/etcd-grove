Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__maybeCommit.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_traceCommit.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_ProgressTracker__Committed.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__maybeCommit.

Module Type RAFT__MAYBECOMMIT_POSTULATES.
  Include TRACECOMMIT.
  Include PROGRESSTRACKER__COMMITTED.
  Include RAFTLOG__MAYBECOMMIT.
End RAFT__MAYBECOMMIT_POSTULATES.
