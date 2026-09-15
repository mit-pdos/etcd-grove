Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__poll.

Module PollPostulates : POLL_POSTULATES.
End PollPostulates.

Module Poll := PollProof PollPostulates.
