Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__becomeCandidate.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__reset.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_traceBecomeCandidate.

Module Type BECOMECANDIDATE_POSTULATES.
  Include RESET.  Include TRACEBECOMECANDIDATE.
End BECOMECANDIDATE_POSTULATES.
