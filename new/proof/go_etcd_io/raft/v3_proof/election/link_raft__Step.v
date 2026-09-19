Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__Step.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__hup.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__becomeFollower.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_voteRespMsgType.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__send_vote.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_stepCandidate_MsgVoteResp.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_stepFollower_MsgVoteResp.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_stepLeader_MsgVoteResp.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_traceReceiveMessage.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__lastEntryID.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raftLog__isUpToDate.

Module StepPostulates : STEP_POSTULATES.
  Include Hup.
  Include BecomeFollower.
  Include VoteRespMsgType.
  Include SendVote.
  Include StepCandidate.
  Include StepFollower.
  Include StepLeader.  Include TraceReceiveMessage.
  Include RaftLogLastEntryID.
  Include RaftLogIsUpToDate.
End StepPostulates.

Module Step := StepProof StepPostulates.
