Require Export New.proof.go_etcd_io.raft.election_proof.proof_unstable__slice.
Require Export New.proof.go_etcd_io.raft.election_proof.link_unstable__mustCheckOutOfBounds.

Module UnstableSlicePostulates : UNSTABLE__SLICE_POSTULATES.
  Include UnstableMustCheckOutOfBounds.
End UnstableSlicePostulates.

Module UnstableSlice := UnstableSliceProof UnstableSlicePostulates.
