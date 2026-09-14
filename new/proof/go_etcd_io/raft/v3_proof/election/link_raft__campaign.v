(** * Link: [raft.raft__campaign]

    [raft__campaign] is in scope but unfinished: the hole is the [Admitted] in
    [proof_raft__campaign.v], not an [Axiom] here. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__campaign.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__becomeCandidate.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__poll.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__send_vote.

Module CampaignPostulates : CAMPAIGN_POSTULATES.
  Include BecomeCandidate.
  Include Poll.
  Include SendVote.
End CampaignPostulates.

Module Campaign := CampaignProof CampaignPostulates.

(** Implicits are not inferred through a folded [_body], and an [Arguments]
    inside the [Module Type] does not survive functor application. *)
Arguments Campaign.wp_raft__campaign {_ _ _ _ _ _ _ _}.
