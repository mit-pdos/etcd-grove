Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__campaign.

Module CampaignProof (P : CAMPAIGN_POSTULATES) : CAMPAIGN.

  Lemma wp_raft__campaign : wp_raft__campaign_body.
  Proof.
  Admitted.

End CampaignProof.
