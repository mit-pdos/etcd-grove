Require Export New.proof.go_etcd_io.raft.election_proof.proof_newLogWithSize.

Module NewLogWithSizePostulates : NEWLOGWITHSIZE_POSTULATES.
End NewLogWithSizePostulates.

Module NewLogWithSize := NewLogWithSizeProof NewLogWithSizePostulates.
