Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__becomePreCandidate.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_ProgressTracker__ResetVotes.

Module Type BECOMEPRECANDIDATE_POSTULATES.
  Include PROGRESSTRACKER__RESETVOTES.
End BECOMEPRECANDIDATE_POSTULATES.
