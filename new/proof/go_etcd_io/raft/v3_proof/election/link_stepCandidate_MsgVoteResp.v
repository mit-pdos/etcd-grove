Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_stepCandidate_MsgVoteResp.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__poll.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__becomeLeader.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_raft__send_vote.

Module StepCandidatePostulates : STEPCANDIDATE_POSTULATES.
  Include Poll.
  Include BecomeLeader.
  Include SendVote.
End StepCandidatePostulates.

Module StepCandidate := StepCandidateProof StepCandidatePostulates.

(* Implicits do not survive a folded [_body]; see notes/gotchas.md. *)
Arguments StepCandidate.wp_stepCandidate_MsgVoteResp {_ _ _ _ _ _ _ _}.
