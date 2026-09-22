Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__mustCheckOutOfBounds.

Module RaftLogMustCheckOutOfBoundsProof (P : RAFTLOG__MUSTCHECKOUTOFBOUNDS_POSTULATES) : RAFTLOG__MUSTCHECKOUTOFBOUNDS.
Import P.

  (** The body reads no field of the log itself outside the two dead
      [Panicf] branches, so [own_raftLog_at] could stay sealed -- except for
      one pure fact.  The last guard is
      [hi > fi + (lastIndex() + 1 - fi)], i.e. [hi > lastIndex() + 1] in
      [w64]; the range premise gives
      [uint hi <= prev.index + |sents| + |uents| + 1 = uint li + 1] over [Z],
      which only rules the guard out if [li + 1] does not wrap.  That is
      [Hnowrap], inside the predicate, so it is peeled off (and the
      predicate re-sealed) before the walk. *)
  Lemma wp_raftLog__mustCheckOutOfBounds_at : wp_raftLog__mustCheckOutOfBounds_at_body.
  Proof.
    intros_ambient.
    intros l prev sents uents lo hi Hrange.
    wp_start as "H". iNamed "H".
    iAssert (⌜ (uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
                + Z.of_nat (length uents) + 1 < 2^64)%Z ⌝ ∗
             own_raftLog_at l prev sents uents)%I with "[Hlog]" as "[%Hnw Hlog]".
    { iDestruct "Hlog" as (lv) "H". iNamed "H". iSplitR; first done.
      iExists lv. iFrame "∗#%". }
    wp_auto.
    rewrite bool_decide_eq_false_2; last lia. wp_auto.
    wp_apply (wp_raftLog__firstIndex_at with "[$Hlog]") as "%fi [Hlog %Hfi]".
    rewrite bool_decide_eq_false_2; last lia. wp_auto.
    wp_apply (wp_raftLog__lastIndex_at with "[$Hlog]") as "%li [Hlog %Hli]".
    rewrite bool_decide_eq_false_2; last word. wp_auto.
    iApply "HΦ". iFrame.
  Qed.

End RaftLogMustCheckOutOfBoundsProof.
