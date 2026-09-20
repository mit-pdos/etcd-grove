Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_payloadSize.

Module PayloadSizePostulates : PAYLOADSIZE_POSTULATES.
End PayloadSizePostulates.

Module PayloadSize := PayloadSizeProof PayloadSizePostulates.
