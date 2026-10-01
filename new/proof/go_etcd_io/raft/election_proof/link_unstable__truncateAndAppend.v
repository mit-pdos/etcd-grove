Require Export New.proof.go_etcd_io.raft.election_proof.proof_unstable__truncateAndAppend.
Require Export New.proof.go_etcd_io.raft.election_proof.link_unstable__slice.

Module UnstableTruncateAndAppendPostulates :
  UNSTABLE__TRUNCATEANDAPPEND_POSTULATES.
  Include UnstableSlice.
End UnstableTruncateAndAppendPostulates.

Module UnstableTruncateAndAppend :=
  UnstableTruncateAndAppendProof UnstableTruncateAndAppendPostulates.
