Require Export New.proof.go_etcd_io.raft.election_proof.proof_raftLog__appliedTo.

Module RaftLogAppliedToPostulates : RAFTLOG__APPLIEDTO_POSTULATES.
End RaftLogAppliedToPostulates.

Module RaftLogAppliedTo := RaftLogAppliedToProof RaftLogAppliedToPostulates.
