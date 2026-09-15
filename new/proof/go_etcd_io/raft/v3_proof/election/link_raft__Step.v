Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__Step.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__hup.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__becomeFollower.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_voteRespMsgType.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__send_vote.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_stepCandidate_MsgVoteResp.

Module StepPostulates : STEP_POSTULATES.
  Include Hup.
  Include BecomeFollower.
  Include VoteRespMsgType.
  Include SendVote.
  Include StepCandidate.
End StepPostulates.

Module Step := StepProof StepPostulates.
