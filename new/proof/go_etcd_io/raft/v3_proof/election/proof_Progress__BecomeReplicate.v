Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_Progress__BecomeReplicate.

Module ProgressBecomeReplicateProof (P : PROGRESS__BECOMEREPLICATE_POSTULATES) : PROGRESS__BECOMEREPLICATE.
Import P.

  Lemma wp_Progress__BecomeReplicate : wp_Progress__BecomeReplicate_body.
  Proof.
    intros_ambient.
    intros pr.

    wp_start as "Hpr". iNamed "Hpr". iNamed "Hinfl". wp_auto.
    wp_apply (wp_Progress__ResetState with "[$Hpv $Hiv]") as "[Hpv Hiv]".
    iApply "HΦ". rewrite /own_progress /own_inflights /=.
    (* after [iExists _] and framing [Hpv] the goal is [Hinfl ∗ %Hnolearner],
       a separating conjunction -- [iExists] cannot apply to it, so split
       first.  [ResetState] carries [IsLearner'] across unchanged, which is
       what discharges the new conjunct. *)
    iExists _. iFrame "Hpv".
    iSplitL "Hiv Hbuf Hbuf_cap".
    (* Do not give the witness: [ResetState] resets the [Inflights] too
       (start/count/bytes zeroed), so it is neither [iv] nor anything already
       named.  Let [iFrame] instantiate the existential from the hypotheses. *)
    (* [simpl] first: the goal's [{|…|}.(Inflights')] projection must reduce to
       [pv.(Inflights')] before [iFrame] can match.  And frame [Hiv] *first*, so
       it fixes the existential to the reset [Inflights] value -- framing [Hbuf]
       first pins the witness to the pre-reset [iv] and then [Hiv] no longer
       matches.  ([Inflights.reset] keeps [buffer'], so [Hbuf]/[Hbuf_cap] fit
       either way.) *)
    { simpl. iFrame "Hiv". iFrame. }
    iPureIntro. exact Hnolearner.
  Qed.

End ProgressBecomeReplicateProof.
