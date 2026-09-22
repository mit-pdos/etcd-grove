Require Export New.proof.go_etcd_io.raft.election_proof.proof_traceBecomeFollower.

Module TraceBecomeFollowerPostulates : TRACEBECOMEFOLLOWER_POSTULATES.
End TraceBecomeFollowerPostulates.

Module TraceBecomeFollower := TraceBecomeFollowerProof TraceBecomeFollowerPostulates.
