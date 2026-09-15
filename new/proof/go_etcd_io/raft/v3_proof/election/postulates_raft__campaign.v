Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_raft__campaign.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__becomeCandidate.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__poll.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__send_vote.

Module Type CAMPAIGN_POSTULATES.
  Include BECOMECANDIDATE.
  Include POLL.
  Include SEND_VOTE.
End CAMPAIGN_POSTULATES.
