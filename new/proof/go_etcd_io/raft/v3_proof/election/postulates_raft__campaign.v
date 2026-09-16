Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_raft__campaign.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__becomeCandidate.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__poll.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__send_vote.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_voteRespMsgType.

Module Type CAMPAIGN_POSTULATES.
  Include BECOMECANDIDATE.
  Include POLL.
  Include SEND_VOTE.
  (* [campaign] calls [voteRespMsgType] for the self-addressed response.
     Missing until 2026-09-16, which made that send unprovable. *)
  Include VOTERESPMSGTYPE.
End CAMPAIGN_POSTULATES.
