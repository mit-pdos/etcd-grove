Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__Step.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__hup.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__becomeFollower.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_voteRespMsgType.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__send.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_stepCandidate.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_stepFollower.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_stepLeader.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_traceReceiveMessage.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__lastEntryID.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__isUpToDate.

Module Type STEP_POSTULATES.
  Include HUP.
  Include BECOMEFOLLOWER.
  Include VOTERESPMSGTYPE.
  Include SEND.
  Include STEPCANDIDATE.
  (* A [MsgVoteResp] falls through [Step]'s type switch to [r.step(m)], which
     is any of the three depending on the role -- on [m.Term > r.Term] the
     term preamble has already run [becomeFollower]. *)
  Include STEPFOLLOWER.
  Include STEPLEADER.  Include TRACERECEIVEMESSAGE.
  Include RAFTLOG__LASTENTRYID.
  Include RAFTLOG__ISUPTODATE.
End STEP_POSTULATES.
