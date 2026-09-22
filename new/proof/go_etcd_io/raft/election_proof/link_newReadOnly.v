Require Export New.proof.go_etcd_io.raft.election_proof.proof_newReadOnly.

Module NewReadOnlyPostulates : NEWREADONLY_POSTULATES.
End NewReadOnlyPostulates.

Module NewReadOnly := NewReadOnlyProof NewReadOnlyPostulates.
