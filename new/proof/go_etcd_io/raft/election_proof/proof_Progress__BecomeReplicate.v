Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Progress__BecomeReplicate.

Module ProgressBecomeReplicateProof (P : PROGRESS__BECOMEREPLICATE_POSTULATES) : PROGRESS__BECOMEREPLICATE.
Import P.

  Lemma wp_Progress__BecomeReplicate : wp_Progress__BecomeReplicate_body.
  Proof.
    intros_ambient.
    intros pr.

    wp_start as "Hpr". iNamed "Hpr". iNamed "Hinfl". wp_auto.
    wp_apply (wp_Progress__ResetState with "[$Hpv $Hiv]") as "[Hpv Hiv]".
    iApply "HΦ". rewrite /own_progress /own_progress_at /own_inflights_at /=.
    (* Do not give the [Inflights] witness: [ResetState] resets the window
       (start/count/bytes zeroed), so it is neither [iv] nor anything already
       named.  Frame [Hiv] *first*, so it fixes the existential to the reset
       value -- framing [Hbuf] first pins the witness to the pre-reset [iv]
       and then [Hiv] no longer matches.  ([Inflights.reset] keeps [buffer'],
       so [Hbuf]/[Hbuf_cap] fit either way.) *)
    iExists _, _. iFrame "Hpv".
    iSplitL "Hiv Hbuf Hbuf_cap".
    { simpl. iFrame "Hiv". iFrame.
      (* the ring invariant survives a reset: [start] and [count] go to [0]
         and the buffer is untouched, so every conjunct is an instance of
         the old one *)
      iPureIntro. destruct Hinfl_ok as (?&?&?&?&?&?).
      rewrite /inflights_ok /=. split_and!; word. }
    (* [ResetState] carries [IsLearner'] across unchanged, and installs
       [StateReplicate] *)
    iPureIntro. split; [ exact Hnolearner | rewrite /progress_state_ok /=; by right; left ].
  Qed.

End ProgressBecomeReplicateProof.
