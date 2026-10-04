Require Export New.proof.go_etcd_io.raft.election_proof.proof_ProgressTracker__Committed.
Require Export New.proof.go_etcd_io.raft.election_proof.link_JointConfig__CommittedIndex.
Require Export New.proof.go_etcd_io.raft.election_proof.link_matchAckIndexer__AckedIndex.

Module ProgressTrackerCommittedPostulates : PROGRESSTRACKER__COMMITTED_POSTULATES.
  Include JointConfigCommittedIndex.
  Include MatchAckIndexerAckedIndex.
End ProgressTrackerCommittedPostulates.

Module ProgressTrackerCommitted :=
  ProgressTrackerCommittedProof ProgressTrackerCommittedPostulates.
