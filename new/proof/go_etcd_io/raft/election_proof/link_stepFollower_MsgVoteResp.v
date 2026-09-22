Require Export New.proof.go_etcd_io.raft.election_proof.proof_stepFollower_MsgVoteResp.

Module StepFollowerPostulates : STEPFOLLOWER_POSTULATES.
End StepFollowerPostulates.

Module StepFollower := StepFollowerProof StepFollowerPostulates.
