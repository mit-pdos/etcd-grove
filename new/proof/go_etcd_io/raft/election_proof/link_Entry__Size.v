Require Export New.proof.go_etcd_io.raft.election_proof.proof_Entry__Size.

Module EntrySizePostulates : ENTRY__SIZE_POSTULATES.
End EntrySizePostulates.

Module EntrySize := EntrySizeProof EntrySizePostulates.
