Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_newReadOnly.

Module NewReadOnlyPostulates : NEWREADONLY_POSTULATES.
End NewReadOnlyPostulates.

Module NewReadOnly := NewReadOnlyProof NewReadOnlyPostulates.
