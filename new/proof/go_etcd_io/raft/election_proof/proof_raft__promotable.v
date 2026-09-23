Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__promotable.

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
    intros cfg r id s Hlent.
    wp_start as "Hphys". iNamed "Hphys".
    iDestruct (own_raftLog_unless_open _ _ Hlent with "Hlog") as (ls Hls) "Hlog".
    iDestruct (own_tracker_unless_open _ _ _ _ _ Hlent with "Htrk") as "Htrk".
    subst id.
    wp_auto.
    destruct (decide (rv.(raft.raft.id') ∈ cfg)) as [Hin|Hnin].
    - (* a voter: its [Progress] is in the map and is not a learner's *)
      wp_apply (wp_tracker_progress_lookup _ _ _ _ _ Hin with "[$Htrk]")
        as "%pr (_ & Hpr & Hprback)".
      iDestruct "Hpr" as (pv iv) "(Hpv & Hinfl & %Hnolearner & %Hst)".
      iDestruct (typed_pointsto_not_null with "Hpv") as %Hnn.
      (* [wp_apply] already reduced [pr != nil] to [negb (bool_decide (pr = null))] *)
      rewrite (bool_decide_eq_false_2 (pr = null) Hnn). simpl.
      wp_auto.
      rewrite Hnolearner. simpl.
      wp_auto.
      wp_apply (P.wp_raftLog__hasNextOrInProgressSnapshot _ _ Hls with "[$Hlog]")
        as "%hb [Hlog %Hhb]".
      subst hb. simpl.
      iDestruct (own_raftLog_unless_close _ _ _ Hlent with "Hlog [//]") as "Hlog".
      iDestruct ("Hprback" with "[Hpv Hinfl]") as "Htrk".
      { iExists pv, iv. rewrite /own_progress. iFrame "∗%". }
      iDestruct (own_tracker_unless_close _ _ _ _ _ Hlent with "Htrk") as "Htrk".
      iApply "HΦ".
      iSplitL.
      { iApply (own_raft_phys_intro with
          "Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc"); done. }
      iPureIntro. rewrite bool_decide_eq_true_2 //.
    - (* not a voter: the lookup misses, [pr == nil] short-circuits to false *)
      iNamed "Htrk".
      assert (s.(nstate.progress) !! rv.(raft.raft.id') = None) as Hnone.
      { apply not_elem_of_dom. rewrite Hprs_dom //. }
      (* the progress map is read-only now, so it stays in the persistent
         context: do not try to re-introduce it *)
      wp_apply (wp_map_lookup1 with "Hprs") as "_".
      rewrite Hnone /=.
      wp_auto.
      iDestruct (own_raftLog_unless_close _ _ _ Hlent with "Hlog [//]") as "Hlog".
      iAssert (own_tracker cfg rv.(raft.raft.trk') s.(nstate.votes)
                 s.(nstate.progress))
        with "[Hvotes Hprogs Hvoters Hlearners HlearnersNext]" as "Htrk".
      { rewrite /own_tracker.
        iExists voters_ref, voters, learners, learnersNext.
        iFrame "∗#%". }
      iDestruct (own_tracker_unless_close _ _ _ _ _ Hlent with "Htrk") as "Htrk".
      iApply "HΦ".
      iSplitL.
      { iApply (own_raft_phys_intro with
          "Hr Hlogger Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc"); done. }
      iPureIntro. rewrite bool_decide_eq_false_2 //.
  Qed.

End RaftPromotableProof.
