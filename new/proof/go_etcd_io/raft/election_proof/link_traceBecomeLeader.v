Require Export New.proof.go_etcd_io.raft.election_proof.proof_traceBecomeLeader.

Module TraceBecomeLeaderPostulates : TRACEBECOMELEADER_POSTULATES.
End TraceBecomeLeaderPostulates.

Module TraceBecomeLeader := TraceBecomeLeaderProof TraceBecomeLeaderPostulates.
