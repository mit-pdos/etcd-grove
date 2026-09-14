(** * Link: [raft.raft__becomeCandidate]

    [raft__becomeCandidate] is proved, so this file carries no [Axiom]. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__becomeCandidate.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__reset.

Module BecomeCandidatePostulates : BECOMECANDIDATE_POSTULATES.
  Include Reset.
End BecomeCandidatePostulates.

Module BecomeCandidate := BecomeCandidateProof BecomeCandidatePostulates.

(** Implicits are not inferred through a folded [_body], and an [Arguments]
    inside the [Module Type] does not survive functor application. *)
Arguments BecomeCandidate.wp_raft__becomeCandidate {_ _ _ _ _ _ _ _}.
