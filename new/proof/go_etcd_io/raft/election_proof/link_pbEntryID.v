Require Export New.proof.go_etcd_io.raft.election_proof.proof_pbEntryID.

Module PbEntryIDPostulates : PBENTRYID_POSTULATES.
End PbEntryIDPostulates.

Module PbEntryID := PbEntryIDProof PbEntryIDPostulates.
