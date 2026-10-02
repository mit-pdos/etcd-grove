Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__maybeCommit.
Require Export New.proof.go_etcd_io.raft.election_proof.link_traceCommit.
Require Export New.proof.go_etcd_io.raft.election_proof.link_ProgressTracker__Committed.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__maybeCommit.

Module RaftMaybeCommitPostulates : RAFT__MAYBECOMMIT_POSTULATES.
  Include TraceCommit.
  Include ProgressTrackerCommitted.
  Include RaftLogMaybeCommit.
End RaftMaybeCommitPostulates.

Module RaftMaybeCommit := RaftMaybeCommitProof RaftMaybeCommitPostulates.
