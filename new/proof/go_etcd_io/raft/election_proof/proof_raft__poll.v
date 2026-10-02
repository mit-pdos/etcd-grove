Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__poll.

Module PollProof (P : POLL_POSTULATES) : POLL.
Import P.

  (** [poll] logs the vote, records it in the tracker, and returns the tally.
      The only model-visible effect is [record_vote]; the leading [if v]
      picks a format string and is otherwise immaterial, so both arms run the
      same tail.

      [RecordVote] and [TallyVotes] are methods of the embedded tracker, so
      they take [&r.trk] and the tracker's own predicate:
      [own_raft_phys_tracker] hands out exactly that, and takes it back at
      the new tally. *)
  Lemma wp_raft__poll : wp_raft__poll_body.
  Proof.
    intros_ambient.
    intros cfg r id s from t v Hcfg_ne.
    wp_start as "Hphys". wp_auto.
    destruct v; wp_auto; (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_apply (wp_raft_load_Term with "Hphys") as "Hphys"; wp_raft_log);
      iDestruct (own_raft_phys_tracker with "Hphys")
        as (tv) "(Htrkf & Htrk & Hback)";
      wp_apply (wp_ProgressTracker__RecordVote with "[$Htrkf $Htrk]")
        as "[Htrkf Htrk]";
      wp_apply (wp_ProgressTracker__TallyVotes _ _ _ _ Hcfg_ne with "[$Htrkf $Htrk]")
        as "%g %rj %res (Htrkf & Htrk & %Hres & %Hwon & %Hlost)";
      iDestruct ("Hback" with "Htrkf Htrk") as "Hphys";
      iApply ("HΦ" $! g rj res); iFrame "Hphys"; iPureIntro; split_and!; done.
  Qed.

End PollProof.
