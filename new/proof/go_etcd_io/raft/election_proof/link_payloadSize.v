Require Export New.proof.go_etcd_io.raft.election_proof.proof_payloadSize.

Module PayloadSizePostulates : PAYLOADSIZE_POSTULATES.
End PayloadSizePostulates.

Module PayloadSize := PayloadSizeProof PayloadSizePostulates.
