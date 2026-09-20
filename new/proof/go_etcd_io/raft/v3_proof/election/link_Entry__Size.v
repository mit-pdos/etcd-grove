Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_Entry__Size.

Module EntrySizePostulates : ENTRY__SIZE_POSTULATES.
End EntrySizePostulates.

Module EntrySize := EntrySizeProof EntrySizePostulates.
