Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__poll.

Module PollPostulates : POLL_POSTULATES.
End PollPostulates.

Module Poll := PollProof PollPostulates.

(* Implicits do not survive a folded [_body]; see notes/gotchas.md. *)
Arguments Poll.wp_raft__poll {_ _ _ _ _ _ _ _}.
