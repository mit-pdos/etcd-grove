Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__poll.
Require Export New.proof.go_etcd_io.raft.election_proof.link_ProgressTracker__RecordVote.
Require Export New.proof.go_etcd_io.raft.election_proof.link_ProgressTracker__TallyVotes.

Module PollPostulates : POLL_POSTULATES.
  Include ProgressTrackerRecordVote.
  Include ProgressTrackerTallyVotes.
End PollPostulates.

Module Poll := PollProof PollPostulates.
