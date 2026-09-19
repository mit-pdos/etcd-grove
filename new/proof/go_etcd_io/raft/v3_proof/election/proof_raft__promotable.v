Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__promotable.

Module RaftPromotableProof (P : RAFT__PROMOTABLE_POSTULATES) : RAFT__PROMOTABLE.
Import P.

  (** [promotable] is

        pr := r.trk.Progress[r.id]
        return pr != nil && !pr.IsLearner && !r.raftLog.hasNextOrInProgressSnapshot()

      Goose renders each [&&] as [If e1 e2 #false], so the proof splits on
      whether [r.id] is a voter, which by [Hprs_dom] is whether it is in the
      progress map:

      - [id ∈ cfg]: [wp_tracker_progress_lookup] hands out that voter's
        [own_progress], whose [pr ↦ pv] makes [pr ≠ nil] and whose
        [Hnolearner] makes [!pr.IsLearner] true; the callee returns [false]
        under [own_raftLog].  Result [true].
      - [id ∉ cfg]: the lookup yields [nil], so the first conjunct is
        [false] and the rest is never evaluated.  Result [false].

      The field reads [r.trk.Progress], [r.id] and [r.raftLog] step through
      [r ↦ rv] by [wp_auto] alone; nothing is written to [r]. *)
  Lemma wp_raft__promotable : wp_raft__promotable_body.
  Proof.
    intros_ambient.
    intros cfg r rv votes.
    wp_start as "(Hr & Htrk & Hlog)".
    wp_auto.
    destruct (decide (rv.(raft.raft.id') ∈ cfg)) as [Hin|Hnin].
    - (* a voter: its [Progress] is in the map and is not a learner's *)
      wp_apply (wp_tracker_progress_lookup _ _ _ _ Hin with "[$Htrk]")
        as "%pr [Hpr Hprback]".
      iDestruct "Hpr" as (pv) "(Hpv & Hinfl & %Hnolearner)".
      iDestruct (typed_pointsto_not_null with "Hpv") as %Hnn.
      (* [wp_apply] already reduced [pr != nil] to [negb (bool_decide (pr = null))] *)
      rewrite (bool_decide_eq_false_2 (pr = null) Hnn). simpl.
      wp_auto.
      rewrite Hnolearner. simpl.
      wp_auto.
      wp_apply (P.wp_raftLog__hasNextOrInProgressSnapshot with "[$Hlog]")
        as "%hb [Hlog %Hhb]".
      subst hb. simpl.
      iApply "HΦ". iFrame "Hr Hlog".
      iSplitL.
      { iApply "Hprback". rewrite /own_progress. iExists pv. iFrame "∗%". }
      iPureIntro. rewrite bool_decide_eq_true_2 //.
    - (* not a voter: the lookup misses, [pr == nil] short-circuits to false *)
      iNamed "Htrk".
      assert (prs !! rv.(raft.raft.id') = None) as Hnone.
      { apply not_elem_of_dom. rewrite Hprs_dom //. }
      wp_apply (wp_map_lookup1 with "Hprs") as "Hprs".
      rewrite Hnone /=.
      wp_auto.
      iApply "HΦ". iFrame "Hr Hlog".
      iSplitL.
      { rewrite /own_tracker.
        iExists prs, voters_ref, voters, learners, learnersNext.
        iFrame "∗%". }
      iPureIntro. rewrite bool_decide_eq_false_2 //.
  Qed.

End RaftPromotableProof.
