Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_stepLeader_MsgVoteResp.

Module StepLeaderPostulates : STEPLEADER_POSTULATES.
End StepLeaderPostulates.

Module StepLeader := StepLeaderProof StepLeaderPostulates.
