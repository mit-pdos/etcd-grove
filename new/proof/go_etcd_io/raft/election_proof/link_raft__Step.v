Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__hup.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__becomeFollower.
Require Export New.proof.go_etcd_io.raft.election_proof.link_voteRespMsgType.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raft__send.
Require Export New.proof.go_etcd_io.raft.election_proof.link_stepCandidate.
Require Export New.proof.go_etcd_io.raft.election_proof.link_stepFollower.
Require Export New.proof.go_etcd_io.raft.election_proof.link_stepLeader.
Require Export New.proof.go_etcd_io.raft.election_proof.link_traceReceiveMessage.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__lastEntryID.
Require Export New.proof.go_etcd_io.raft.election_proof.link_raftLog__isUpToDate.

Module StepPostulates : STEP_POSTULATES.
  Include Hup.
  Include BecomeFollower.
  Include VoteRespMsgType.
  Include Send.
  Include StepCandidate.
  Include StepFollower.
  Include StepLeader.  Include TraceReceiveMessage.
  Include RaftLogLastEntryID.
  Include RaftLogIsUpToDate.
End StepPostulates.

Module Step := StepProof StepPostulates.
