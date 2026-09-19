Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_raft__becomeCandidate.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__reset.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_traceBecomeCandidate.

Module Type BECOMECANDIDATE_POSTULATES.
  Include RESET.  Include TRACEBECOMECANDIDATE.
End BECOMECANDIDATE_POSTULATES.
