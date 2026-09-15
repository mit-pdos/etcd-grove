Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_stepCandidate_MsgVoteResp.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__poll.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__becomeLeader.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__send_vote.

Module Type STEPCANDIDATE_POSTULATES.
  Include POLL.
  Include BECOMELEADER.
  Include SEND_VOTE.
End STEPCANDIDATE_POSTULATES.
