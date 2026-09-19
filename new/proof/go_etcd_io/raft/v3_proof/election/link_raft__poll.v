Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__poll.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_ProgressTracker__RecordVote.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_ProgressTracker__TallyVotes.

Module PollPostulates : POLL_POSTULATES.
  Include ProgressTrackerRecordVote.
  Include ProgressTrackerTallyVotes.
End PollPostulates.

Module Poll := PollProof PollPostulates.
