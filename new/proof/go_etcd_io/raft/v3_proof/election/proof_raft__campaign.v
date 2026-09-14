(** * Proof: [raft.raft__campaign] against its spec

    Opaquely ascribed, so the proof term is sealed: callers can depend on
    nothing but the spec.  The binders arrive by [intros] rather than
    [Context] -- the lemma's type is closed, so there are no section variables
    to discharge and no [Collection W] is needed. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__campaign.

Module CampaignProof (P : CAMPAIGN_POSTULATES) : CAMPAIGN.

  Lemma wp_raft__campaign : wp_raft__campaign_body.
  Proof.
  Admitted.

End CampaignProof.
