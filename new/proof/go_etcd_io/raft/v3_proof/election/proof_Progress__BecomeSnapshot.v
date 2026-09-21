Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_Progress__BecomeSnapshot.

Module ProgressBecomeSnapshotProof (P : PROGRESS__BECOMESNAPSHOT_POSTULATES)
  : PROGRESS__BECOMESNAPSHOT.
Import P.

  Lemma wp_Progress__BecomeSnapshot : wp_Progress__BecomeSnapshot_body.
  Proof.
    intros_ambient.
    intros pr snapshoti.

    wp_start as "Hpr". iNamed "Hpr". iNamed "Hinfl". wp_auto.
    (* [wp_apply … as] runs [wp_auto] for us, so the three stores that follow
       the [ResetState] call are already taken *)
    wp_apply (wp_Progress__ResetState with "[$Hpv $Hiv]") as "[Hpv Hiv]".
    iApply "HΦ". rewrite /own_progress /own_progress_at /own_inflights_at /=.
    (* as in [proof_Progress__BecomeReplicate.v]: frame the reset [Inflights]
       first so that it, and not the pre-reset value, fixes the existential *)
    iExists _, _. iFrame "Hpv".
    iSplitL "Hiv Hbuf Hbuf_cap".
    { simpl. iFrame "Hiv". iFrame.
      iPureIntro. destruct Hinfl_ok as (?&?&?&?&?&?).
      rewrite /inflights_ok /=. split_and!; word. }
    (* [ResetState] carries [IsLearner'] across and installs [StateSnapshot],
       which is [W64 2] -- the third disjunct of [progress_state_ok] *)
    iPureIntro.
    split; [ exact Hnolearner | rewrite /progress_state_ok /=; by right; right ].
  Qed.

End ProgressBecomeSnapshotProof.
