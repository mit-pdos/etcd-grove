(** * Link: [raft.raft__hup]

    [raft__hup] is in scope but unfinished: the hole is the [Admitted] in
    [proof_raft__hup.v], not an [Axiom] here. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__hup.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__campaign.

Module HupPostulates : HUP_POSTULATES.
  Include Campaign.
End HupPostulates.

Module Hup := HupProof HupPostulates.

(** Implicits are not inferred through a folded [_body], and an [Arguments]
    inside the [Module Type] does not survive functor application. *)
Arguments Hup.wp_raft__hup {_ _ _ _ _ _ _ _}.
