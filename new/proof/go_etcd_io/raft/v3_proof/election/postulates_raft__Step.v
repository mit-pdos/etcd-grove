Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_raft__Step.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__hup.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__becomeFollower.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_voteRespMsgType.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__send_vote.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_stepCandidate_MsgVoteResp.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_stepFollower_MsgVoteResp.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_stepLeader_MsgVoteResp.

Module Type STEP_POSTULATES.
  Include HUP.
  Include BECOMEFOLLOWER.
  Include VOTERESPMSGTYPE.
  Include SEND_VOTE.
  Include STEPCANDIDATE.
  (* A [MsgVoteResp] falls through [Step]'s type switch to [r.step(m)], which
     is any of the three depending on the role -- on [m.Term > r.Term] the
     term preamble has already run [becomeFollower]. *)
  Include STEPFOLLOWER.
  Include STEPLEADER.
End STEP_POSTULATES.
