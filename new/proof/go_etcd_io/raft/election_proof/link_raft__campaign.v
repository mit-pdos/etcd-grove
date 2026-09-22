Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__campaign.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__becomeCandidate.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__poll.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__send.
Require Export New.proof.go_etcd_io.raft.election_proof.link_voteRespMsgType.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__promotable.
Require Export New.proof.go_etcd_io.raft.election_proof.link_JointConfig__IDs.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__lastEntryID.
Require Export New.proof.go_etcd_io.raft.election_proof.link_slices_Sort.

Module CampaignPostulates : CAMPAIGN_POSTULATES.
  Include BecomeCandidate.
  Include Poll.
  Include Send.
  Include VoteRespMsgType.  Include RaftPromotable.
  Include JointConfigIDs.
  Include RaftLogLastEntryID.
  Include SlicesSort.
End CampaignPostulates.

Module Campaign := CampaignProof CampaignPostulates.
