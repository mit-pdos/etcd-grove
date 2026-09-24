Require Export New.proof.go_etcd_io.raft.election_proof.proof_MajorityConfig__Slice.
Require Export New.proof.go_etcd_io.raft.election_proof.link_slices_Sort.

Module MajorityConfigSlicePostulates : MAJORITYCONFIG__SLICE_POSTULATES.
  Include SlicesSort.
End MajorityConfigSlicePostulates.

Module MajorityConfigSlice := MajorityConfigSliceProof MajorityConfigSlicePostulates.
