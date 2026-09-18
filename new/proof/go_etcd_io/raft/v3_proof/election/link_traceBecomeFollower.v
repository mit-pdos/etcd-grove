Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_traceBecomeFollower.

Module TraceBecomeFollowerPostulates : TRACEBECOMEFOLLOWER_POSTULATES.
End TraceBecomeFollowerPostulates.

Module TraceBecomeFollower := TraceBecomeFollowerProof TraceBecomeFollowerPostulates.
