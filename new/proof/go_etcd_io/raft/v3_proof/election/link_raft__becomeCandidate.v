Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__becomeCandidate.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__reset.

Module BecomeCandidatePostulates : BECOMECANDIDATE_POSTULATES.
  Include Reset.
End BecomeCandidatePostulates.

Module BecomeCandidate := BecomeCandidateProof BecomeCandidatePostulates.

(* Implicits do not survive a folded [_body]; see notes/gotchas.md. *)
Arguments BecomeCandidate.wp_raft__becomeCandidate {_ _ _ _ _ _ _ _}.
