Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__reset.
Require Export New.proof.go_etcd_io.raft.election_proof.link_ProgressTracker__ResetVotes.
Require Export New.proof.go_etcd_io.raft.election_proof.link_ProgressTracker__Visit.
Require Export New.proof.go_etcd_io.raft.election_proof.link_tracker_NewInflights.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.link_newReadOnly.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__resetRandomizedElectionTimeout.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__abortLeaderTransfer.

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
