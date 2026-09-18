Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__poll.

Module PollProof (P : POLL_POSTULATES) : POLL.
Import P.

  (** [poll] logs the vote, records it in the tracker, and returns the tally.
      The only model-visible effect is [record_vote]; the leading [if v]
      picks a format string and is otherwise immaterial, so both arms run the
      same tail.

      [RecordVote] and [TallyVotes] want the tracker's *location*.  A caller
      holding the whole struct gets it from the generated [AccessStrict]
      instance ([raft_access_load_trk]), which hands out the one field and a
      wand to put it back -- the *load* form suffices because neither call
      changes the tracker value.  That is cheaper and far more robust than
      unsealing [r ↦ rv] into its 35 field points-tos: [iNamed] does not fire
      on the unsealed conjunction, so that route needs a positional
      [iDestruct] listing every field. *)
  Lemma wp_raft__poll : wp_raft__poll_body.
  Proof.
    intros_ambient.
    intros cfg r id s from t v.
    wp_start as "Hphys". iNamed "Hphys". wp_auto.
    destruct v.
    - (* a granted vote *)
      wp_auto.
      wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
      wp_auto. rewrite Hlok.
      wp_apply (wp_Logger__logf with "Hlogger").
      { rewrite /log_methods. set_solver. }
      (* pin the *load* instance: with [A = A'] the store instance also
         unifies, and it hands back [rv <| trk' := rv.(trk') |>], which is
         not syntactically [rv]. *)
      iDestruct (access_strict
                   (A := r.[raft.raft.t, "trk"] ↦ rv.(raft.raft.trk'))
                   (A' := r.[raft.raft.t, "trk"] ↦ rv.(raft.raft.trk'))
                   (P := r ↦ rv) (P' := r ↦ rv)
                   with "Hr") as "[Htrkf Hrback]".
      wp_apply (wp_ProgressTracker__RecordVote with "[$Htrkf $Htrk]")
        as "[Htrkf Htrk]".
      wp_apply (wp_ProgressTracker__TallyVotes with "[$Htrkf $Htrk]")
        as "%g %rj %res (Htrkf & Htrk & %Hres & %Hwon & %Hlost)".
      iDestruct ("Hrback" with "Htrkf") as "Hr".
      iApply ("HΦ" $! g rj res).
      iSplitL "Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc".
      { rewrite /own_raft_phys. iExists rv, msgs, msgsAA, lok.
        simpl. iFrame "∗#%". }
      iPureIntro. split_and!; done.
    - (* a rejection *)
      wp_auto.
      wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
      wp_auto. rewrite Hlok.
      wp_apply (wp_Logger__logf with "Hlogger").
      { rewrite /log_methods. set_solver. }
      (* pin the *load* instance: with [A = A'] the store instance also
         unifies, and it hands back [rv <| trk' := rv.(trk') |>], which is
         not syntactically [rv]. *)
      iDestruct (access_strict
                   (A := r.[raft.raft.t, "trk"] ↦ rv.(raft.raft.trk'))
                   (A' := r.[raft.raft.t, "trk"] ↦ rv.(raft.raft.trk'))
                   (P := r ↦ rv) (P' := r ↦ rv)
                   with "Hr") as "[Htrkf Hrback]".
      wp_apply (wp_ProgressTracker__RecordVote with "[$Htrkf $Htrk]")
        as "[Htrkf Htrk]".
      wp_apply (wp_ProgressTracker__TallyVotes with "[$Htrkf $Htrk]")
        as "%g %rj %res (Htrkf & Htrk & %Hres & %Hwon & %Hlost)".
      iDestruct ("Hrback" with "Htrkf") as "Hr".
      iApply ("HΦ" $! g rj res).
      iSplitL "Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc".
      { rewrite /own_raft_phys. iExists rv, msgs, msgsAA, lok.
        simpl. iFrame "∗#%". }
      iPureIntro. split_and!; done.
  Qed.

End PollProof.
