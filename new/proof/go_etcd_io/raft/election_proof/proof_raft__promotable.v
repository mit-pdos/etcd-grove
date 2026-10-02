Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__promotable.

Module RaftPromotableProof (P : RAFT__PROMOTABLE_POSTULATES) : RAFT__PROMOTABLE.
Import P.

  (** [promotable] is

        pr := r.trk.Progress[r.id]
        return pr != nil && !pr.IsLearner && !r.raftLog.hasNextOrInProgressSnapshot()

      Goose renders each [&&] as [If e1 e2 #false], so the proof splits on
      whether [r.id] is a voter, which by the tracker's domain fact is
      whether it is in the progress map:

      - [id ∈ cfg]: [wp_tracker_progress_lookup] hands out that voter's
        [own_progress], whose [pr ↦ pv] makes [pr ≠ nil] and whose
        [Hnolearner] makes [!pr.IsLearner] true; the callee returns [false]
        under [own_raftLog].  Result [true].
      - [id ∉ cfg]: the lookup yields [nil], so the first conjunct is
        [false] and the rest is never evaluated.  Result [false].

      [r.id] and [r.raftLog] are read with their field lemmas; the map
      [r.trk.Progress] is read off the tracker object that
      [own_raft_phys_tracker] hands out, and the log's method runs on what
      [own_raft_phys_log] hands out.  Nothing is written to [r]. *)
  Lemma wp_raft__promotable : wp_raft__promotable_body.
  Proof.
    intros_ambient.
    intros cfg r id s.
    wp_start as "Hphys". wp_auto.
    wp_apply (wp_raft_load_id with "Hphys") as "Hphys".
    iDestruct (own_raft_phys_tracker with "Hphys")
      as (tv) "(Htrkf & Htrk & Hback)".
    wp_auto.
    destruct (decide (id ∈ cfg)) as [Hin|Hnin].
    - (* a voter: its [Progress] is in the map and is not a learner's *)
      wp_apply (wp_tracker_progress_lookup _ _ _ _ Hin with "[$Htrk]")
        as "%pr (_ & %p & %Hpvs & Hpr & Hprback)".
      iDestruct "Hpr" as (pv) "(Hpv & Hinfl & %Habs)".
      pose proof Habs as Hnolearner.
      apply progress_abs_Some in Hnolearner as (Hnolearner & _).
      iDestruct (typed_pointsto_not_null with "Hpv") as %Hnn.
      (* [wp_apply] already reduced [pr != nil] to [negb (bool_decide (pr = null))] *)
      rewrite (bool_decide_eq_false_2 (pr = null) Hnn). simpl.
      wp_auto.
      rewrite Hnolearner. simpl.
      wp_auto.
      iDestruct ("Hprback" $! p with "[Hpv Hinfl]") as "Htrk".
      { iExists pv. iFrame "∗%". }
      (* written back at the values it was read at *)
      rewrite insert_id //.
      iDestruct ("Hback" with "Htrkf Htrk") as "Hphys".
      iDestruct (own_raft_phys_eq _ _ _ _ s with "Hphys") as "Hphys".
      { by destruct s. }
      wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
      iDestruct (own_raft_phys_log_same with "Hphys") as "(Hlog & Hback)".
      wp_apply (P.wp_raftLog__hasNextOrInProgressSnapshot with "[$Hlog]")
        as "%hb [Hlog %Hhb]".
      subst hb.
      iDestruct ("Hback" with "Hlog") as "Hphys".
      iApply "HΦ". iFrame "Hphys".
      iPureIntro.
      destruct (s.(nstate.logst).(logstate.snap)) as [sid|].
      + rewrite (bool_decide_eq_true_2 (Some sid ≠ None)) //.
        rewrite (bool_decide_eq_false_2 (id ∈ cfg ∧ Some sid = None)) //.
        intros [_ Hc]. discriminate Hc.
      + rewrite (bool_decide_eq_false_2 (None ≠ None)); last (by intros ?).
        rewrite (bool_decide_eq_true_2 (id ∈ cfg ∧ (None : option raft.entryID.t) = None)) //.
    - (* not a voter: the lookup misses, [pr == nil] short-circuits to false *)
      iDestruct (own_tracker_progress_map with "Htrk") as "(#Hprs & %Hdom & Htrk)".
      assert (s.(nstate.progress) !! id = None) as Hnone.
      { apply not_elem_of_dom. rewrite Hdom //. }
      (* the progress map is read-only now, so it stays in the persistent
         context: do not try to re-introduce it *)
      wp_apply (wp_map_lookup1 with "Hprs") as "_".
      rewrite Hnone /=.
      wp_auto.
      iDestruct ("Hback" with "Htrkf Htrk") as "Hphys".
      iApply "HΦ".
      iSplitL.
      { iApply (own_raft_phys_eq with "Hphys"). by destruct s. }
      iPureIntro. rewrite bool_decide_eq_false_2 //. intros [? _]. done.
  Qed.

End RaftPromotableProof.
