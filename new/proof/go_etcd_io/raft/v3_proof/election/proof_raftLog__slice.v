Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raftLog__slice.

Module RaftLogSliceProof (P : RAFTLOG__SLICE_POSTULATES) : RAFTLOG__SLICE.
Import P.

  Lemma wp_raftLog__slice_at : wp_raftLog__slice_at_body.
  Proof.
    intros_ambient.
    intros l prev sents uents lo hi maxSize Hrange.
  Admitted.

End RaftLogSliceProof.
