Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raftLog__mustCheckOutOfBounds.

Module RaftLogMustCheckOutOfBoundsProof (P : RAFTLOG__MUSTCHECKOUTOFBOUNDS_POSTULATES) : RAFTLOG__MUSTCHECKOUTOFBOUNDS.
Import P.

  (** [own_raftLog_at] stays sealed throughout: the body reads no field of
      the log itself outside the two dead [Panicf] branches, and the
      [firstIndex]/[lastIndex] specs want it sealed.  [Hnowrap] (inside the
      predicate) is not needed: [lastIndex + 1] does not wrap because the
      range premise bounds [hi] by it and [hi] is a [w64]. *)
  Lemma wp_raftLog__mustCheckOutOfBounds_at : wp_raftLog__mustCheckOutOfBounds_at_body.
  Proof.
    intros_ambient.
    intros l prev sents uents lo hi Hrange.
    wp_start as "H". iNamed "H". wp_auto.
    rewrite bool_decide_eq_false_2; last lia. wp_auto.
    wp_apply (wp_raftLog__firstIndex_at with "[$Hlog]") as "%fi [Hlog %Hfi]".
    rewrite bool_decide_eq_false_2; last lia. wp_auto.
    wp_apply (wp_raftLog__lastIndex_at with "[$Hlog]") as "%li [Hlog %Hli]".
    rewrite bool_decide_eq_false_2; last word. wp_auto.
    iApply "HΦ". iFrame.
  Qed.

End RaftLogMustCheckOutOfBoundsProof.
