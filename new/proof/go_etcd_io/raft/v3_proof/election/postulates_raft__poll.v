Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_raft__poll.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_ProgressTracker__RecordVote.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_ProgressTracker__TallyVotes.

Module Type POLL_POSTULATES.
  Include PROGRESSTRACKER__RECORDVOTE.
  Include PROGRESSTRACKER__TALLYVOTES.
End POLL_POSTULATES.
