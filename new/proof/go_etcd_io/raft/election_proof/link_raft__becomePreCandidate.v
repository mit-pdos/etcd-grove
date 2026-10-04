Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__becomePreCandidate.
Require Export New.proof.go_etcd_io.raft.election_proof.link_ProgressTracker__ResetVotes.

Module BecomePreCandidatePostulates : BECOMEPRECANDIDATE_POSTULATES.
  Include ProgressTrackerResetVotes.
End BecomePreCandidatePostulates.

Module BecomePreCandidate := BecomePreCandidateProof BecomePreCandidatePostulates.
