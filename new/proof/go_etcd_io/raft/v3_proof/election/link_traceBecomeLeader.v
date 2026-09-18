Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_traceBecomeLeader.

Module TraceBecomeLeaderPostulates : TRACEBECOMELEADER_POSTULATES.
End TraceBecomeLeaderPostulates.

Module TraceBecomeLeader := TraceBecomeLeaderProof TraceBecomeLeaderPostulates.
