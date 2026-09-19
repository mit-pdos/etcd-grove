Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__reset.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_ProgressTracker__ResetVotes.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_ProgressTracker__Visit.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_tracker_NewInflights.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_newReadOnly.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__resetRandomizedElectionTimeout.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__abortLeaderTransfer.

Module ResetPostulates : RESET_POSTULATES.
  Include ProgressTrackerResetVotes.
  Include ProgressTrackerVisit.
  Include TrackerNewInflights.
  Include RaftLogLastIndex.
  Include NewReadOnly.
  Include RaftResetRandomizedElectionTimeout.
  Include RaftAbortLeaderTransfer.
End ResetPostulates.

Module Reset := ResetProof ResetPostulates.
