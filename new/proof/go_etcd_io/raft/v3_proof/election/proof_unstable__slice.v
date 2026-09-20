Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_unstable__slice.

Module UnstableSliceProof (P : UNSTABLE__SLICE_POSTULATES) : UNSTABLE__SLICE.
Import P.

  Lemma wp_unstable__slice : wp_unstable__slice_body.
  Proof.
    intros_ambient.
    intros u uv uents lo hi Hrange Hnw.
  Admitted.

End UnstableSliceProof.
