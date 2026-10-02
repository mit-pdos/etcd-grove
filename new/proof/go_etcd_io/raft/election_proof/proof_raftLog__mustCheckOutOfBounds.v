Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__mustCheckOutOfBounds.

Module RaftLogMustCheckOutOfBoundsProof (P : RAFTLOG__MUSTCHECKOUTOFBOUNDS_POSTULATES) : RAFTLOG__MUSTCHECKOUTOFBOUNDS.
Import P.

  (** The body reads no field of the log itself outside the two dead
      [Panicf] branches, so [own_raftLog] could stay sealed -- except for
      one pure fact.  The last guard is
      [hi > fi + (lastIndex() + 1 - fi)], i.e. [hi > lastIndex() + 1] in
      [w64]; the range premise gives
      [uint hi <= prev.index + |sents| + |uents| + 1 = uint li + 1] over [Z],
      which only rules the guard out if [li + 1] does not wrap.  That is
      [Hnowrap], inside the predicate, so it is peeled off (and the
      predicate re-sealed) before the walk. *)
  Lemma wp_raftLog__mustCheckOutOfBounds : wp_raftLog__mustCheckOutOfBounds_body.
  Proof.
    intros_ambient.
    intros l ls lo hi Hrange.
    destruct ls as [prev sents uents lcm lap snap]; logstate_simpl.
    wp_start as "H". iNamed "H".
    iDestruct (own_raftLog_nowrap with "Hlog") as "[%Hnw Hlog]".
    logstate_simpl.
    wp_auto.
    rewrite bool_decide_eq_false_2; last lia. wp_auto.
    wp_apply (wp_raftLog__firstIndex _ (logstate.mk prev sents uents lcm lap snap) with "[$Hlog]") as "%fi [Hlog %Hfi]". logstate_simpl.
    rewrite bool_decide_eq_false_2; last lia. wp_auto.
    wp_apply (wp_raftLog__lastIndex _ (logstate.mk prev sents uents lcm lap snap) with "[$Hlog]") as "%li [Hlog %Hli]". logstate_simpl.
    rewrite bool_decide_eq_false_2; last word. wp_auto.
    iApply "HΦ". iFrame.
  Qed.

End RaftLogMustCheckOutOfBoundsProof.
