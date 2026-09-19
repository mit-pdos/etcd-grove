Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_slices_Sort.

Module SlicesSortProof (P : SLICES_SORT_POSTULATES) : SLICES_SORT.

  (** Trust boundary: an [Axiom] inside the functor rather than an
      [Admitted] [Lemma], so that it still counts as an assumption
      under [Print Assumptions] and under the greps in
      notes/STATUS.md.  See that file for why it may be assumed. *)
  Axiom wp_slices_Sort : wp_slices_Sort_body.

End SlicesSortProof.
