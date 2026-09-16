Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_stepFollower_MsgVoteResp.

Module StepFollowerPostulates : STEPFOLLOWER_POSTULATES.
End StepFollowerPostulates.

Module StepFollower := StepFollowerProof StepFollowerPostulates.
