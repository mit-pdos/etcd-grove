Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_slices_Sort.

Module SlicesSortPostulates : SLICES_SORT_POSTULATES.
End SlicesSortPostulates.

Module SlicesSort := SlicesSortProof SlicesSortPostulates.
