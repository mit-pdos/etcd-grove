Require Export New.proof.go_etcd_io.raft.election_proof.postulates_ProgressTracker__RecordVote.

Module ProgressTrackerRecordVoteProof (P : PROGRESSTRACKER__RECORDVOTE_POSTULATES) : PROGRESSTRACKER__RECORDVOTE.

  Lemma wp_ProgressTracker__RecordVote : wp_ProgressTracker__RecordVote_body.
  Proof.
    intros_ambient.
    intros cfg trk tv votes prs from v.

    wp_start as "[Htrk Hown]". iNamed "Hown". wp_auto.
    wp_apply (wp_map_lookup2 with "Hvotes") as "Hvotes".
    case_bool_decide as Hok.
    - (* already voted: first write wins, the map is left alone *)
      wp_auto.
      iApply "HΦ". iFrame "Htrk".
      destruct Hok as [v0 Hv0].
      rewrite /own_tracker /record_vote Hv0 /=.
      iExists voters_ref, voters, learners, learnersNext.
      iFrame "∗#%".
    - (* first vote from [from] *)
      wp_auto.
      apply eq_None_not_Some in Hok.
      (* no trailing [wp_auto]: [wp_apply … as] already ran it -- gotchas.md *)
      wp_apply (wp_map_insert with "Hvotes") as "Hvotes".
      iApply "HΦ". iFrame "Htrk".
      rewrite /own_tracker /record_vote Hok /=.
      iExists voters_ref, voters, learners, learnersNext.
      iFrame "∗#%".
  Qed.

End ProgressTrackerRecordVoteProof.
