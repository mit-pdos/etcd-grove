Require Export New.proof.go_etcd_io.raft.election_proof.spec_stepCandidate.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__poll.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__becomeLeader.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__becomeFollower.

(** [stepCandidate]'s direct callees on the [MsgVoteResp] path: [poll], then
    [becomeLeader] (on [VoteWon]) or [becomeFollower] (on [VoteLost]).

    [SEND_VOTE] used to be here and was never reachable: [stepCandidate] does
    not call [send] itself -- the sends on this path are inside
    [becomeLeader]/[bcastAppend], which carry their own specs. [BECOMEFOLLOWER]
    was missing, which made the [VoteLost] arm unprovable. Corrected
    2026-09-16.  [MsgApp] adds [becomeFollower] (already here) and
    [handleAppendEntries] (2026-10-01); [MsgHeartbeat] adds
    [handleHeartbeat] (2026-10-02); [MsgProp] only logs. *)
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__bcastAppend.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__handleAppendEntries.
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__handleHeartbeat.

Module Type STEPCANDIDATE_POSTULATES.
  Include POLL.
  Include BECOMELEADER.
  Include BECOMEFOLLOWER.  Include RAFT__BCASTAPPEND.
  Include RAFT__HANDLEAPPENDENTRIES.
  Include RAFT__HANDLEHEARTBEAT.
End STEPCANDIDATE_POSTULATES.
