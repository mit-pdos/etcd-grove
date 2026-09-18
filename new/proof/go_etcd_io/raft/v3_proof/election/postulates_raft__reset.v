Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_raft__reset.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_ProgressTracker__ResetVotes.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_ProgressTracker__Visit.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_tracker_NewInflights.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raftLog__lastIndex.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_newReadOnly.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__resetRandomizedElectionTimeout.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__abortLeaderTransfer.

Module Type RESET_POSTULATES.
  Include PROGRESSTRACKER__RESETVOTES.
  Include PROGRESSTRACKER__VISIT.
  Include TRACKER_NEWINFLIGHTS.
  Include RAFTLOG__LASTINDEX.
  Include NEWREADONLY.
  Include RAFT__RESETRANDOMIZEDELECTIONTIMEOUT.
  Include RAFT__ABORTLEADERTRANSFER.
End RESET_POSTULATES.
