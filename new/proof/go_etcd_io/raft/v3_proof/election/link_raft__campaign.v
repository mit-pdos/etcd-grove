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
