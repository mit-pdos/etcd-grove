Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_unstable__slice.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.link_unstable__mustCheckOutOfBounds.

Module UnstableSlicePostulates : UNSTABLE__SLICE_POSTULATES.
  Include UnstableMustCheckOutOfBounds.
End UnstableSlicePostulates.

Module UnstableSlice := UnstableSliceProof UnstableSlicePostulates.
