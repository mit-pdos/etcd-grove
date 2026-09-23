Require Export New.proof.go_etcd_io.raft.election_proof.postulates_unstable__mustCheckOutOfBounds.

Module UnstableMustCheckOutOfBoundsProof (P : UNSTABLE__MUSTCHECKOUTOFBOUNDS_POSTULATES) : UNSTABLE__MUSTCHECKOUTOFBOUNDS.

  (** Two [if]s, both guarding a [Panicf]; the range premise makes both
      conditions [false].  [upper = offset + uint64(len(entries))] needs the
      slice's length, whence [own_slice_len], and the no-wrap premise so
      that the sum is exact. *)
  Lemma wp_unstable__mustCheckOutOfBounds : wp_unstable__mustCheckOutOfBounds_body.
  Proof.
    intros_ambient.
    intros u uv uents dq lo hi Hrange Hnw.
    wp_start as "H". iNamed "H". wp_auto.
    iDestruct (own_slice_len with "Hents") as %[Hlen1 Hlen2].
    rewrite bool_decide_eq_false_2; last lia. wp_auto.
    rewrite bool_decide_eq_false_2; last lia. wp_auto.
    rewrite bool_decide_eq_false_2; last word. wp_auto.
    iApply "HΦ". iFrame.
  Qed.

End UnstableMustCheckOutOfBoundsProof.
