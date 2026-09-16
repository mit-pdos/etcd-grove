Require Export New.proof.go_etcd_io.raft.v3_proof.election.spec_stepCandidate_MsgVoteResp.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__poll.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__becomeLeader.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__becomeFollower.

(** [stepCandidate]'s direct callees on the [MsgVoteResp] path: [poll], then
    [becomeLeader] (on [VoteWon]) or [becomeFollower] (on [VoteLost]).

    [SEND_VOTE] used to be here and was never reachable: [stepCandidate] does
    not call [send] itself -- the sends on this path are inside
    [becomeLeader]/[bcastAppend], which carry their own specs. [BECOMEFOLLOWER]
    was missing, which made the [VoteLost] arm unprovable. Corrected
    2026-09-16. *)
Module Type STEPCANDIDATE_POSTULATES.
  Include POLL.
  Include BECOMELEADER.
  Include BECOMEFOLLOWER.
End STEPCANDIDATE_POSTULATES.
