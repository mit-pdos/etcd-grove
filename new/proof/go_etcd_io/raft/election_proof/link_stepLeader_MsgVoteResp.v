Require Export New.proof.go_etcd_io.raft.election_proof.proof_stepLeader_MsgVoteResp.

Module StepLeaderPostulates : STEPLEADER_POSTULATES.
End StepLeaderPostulates.

Module StepLeader := StepLeaderProof StepLeaderPostulates.
