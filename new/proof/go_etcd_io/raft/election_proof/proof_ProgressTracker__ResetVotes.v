Require Export New.proof.go_etcd_io.raft.election_proof.postulates_ProgressTracker__ResetVotes.

Module ProgressTrackerResetVotesProof (P : PROGRESSTRACKER__RESETVOTES_POSTULATES) : PROGRESSTRACKER__RESETVOTES.

  Lemma wp_ProgressTracker__ResetVotes : wp_ProgressTracker__ResetVotes_body.
  Proof.
    intros_ambient.
    intros cfg trk tv votes prs pvs.

    wp_start as "[Htrk Hown]". iNamed "Hown". wp_auto.
    wp_apply wp_map_make1. iIntros "%votesRef Hvotes_new". wp_auto.
    iApply ("HΦ" $! votesRef). iFrame "Htrk".
    rewrite /own_tracker /=.
    iExists voters_ref, voters, learners, learnersNext.
    iFrame "Hvotes_new". iFrame "∗#%".
  Qed.

End ProgressTrackerResetVotesProof.
