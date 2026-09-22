Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__becomeCandidate.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__reset.
Require Export New.proof.go_etcd_io.raft.election_proof.link_traceBecomeCandidate.

Module BecomeCandidatePostulates : BECOMECANDIDATE_POSTULATES.
  Include Reset.  Include TraceBecomeCandidate.
End BecomeCandidatePostulates.

Module BecomeCandidate := BecomeCandidateProof BecomeCandidatePostulates.
