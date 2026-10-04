Require Export New.proof.go_etcd_io.raft.election_proof.postulates_ProgressTracker__Committed.

Module ProgressTrackerCommittedProof (P : PROGRESSTRACKER__COMMITTED_POSTULATES)
  : PROGRESSTRACKER__COMMITTED.
Import P.

  (** Open [own_tracker]; load [p.Voters] (the array value) and hand it to
      [JointConfig.CommittedIndex] with the voter map and the progress map
      with its [Progress] objects ([own_progress_map]) as the indexer's
      resource -- the indexer is [matchAckIndexer(p.Progress)], whose
      contract comes from [matchAckIndexer.AckedIndex]'s triple -- then
      close [own_tracker] again around the voter map it hands back. *)
  Lemma wp_ProgressTracker__Committed : wp_ProgressTracker__Committed_body.
  Proof.
    intros_ambient.
    intros cfg trk tv [votes prs pvs].
    wp_start as "(Htrk & Hown)". iNamed "Hown". trk_simpl.
    wp_auto.
    iAssert (is_AckedIndexer
               (interface.mk_ok tracker.matchAckIndexer
                  #(tv.(tracker.ProgressTracker.Progress')))
               (own_progress_map tv.(tracker.ProgressTracker.Progress') prs pvs)
               (pvs_acked pvs))%I as "#Hidx".
    { iExists _. iSplit; first done.
      iIntros "!>" (id Ψ) "!> HP HΨ". simpl.
      wp_apply (wp_matchAckIndexer__AckedIndex with "[$HP]") as "HP".
      by iApply "HΨ". }
    iAssert (own_progress_map tv.(tracker.ProgressTracker.Progress') prs pvs)%I
      with "[Hprogs]" as "HP".
    { rewrite /own_progress_map. iFrame "∗#". }
    (* the [Voters] field's location, out of [trk ↦ tv] *)
    iDestruct (access_strict
                 (A := trk.[tracker.ProgressTracker.t, "Config"]
                         ↦ tv.(tracker.ProgressTracker.Config'))
                 (A' := trk.[tracker.ProgressTracker.t, "Config"]
                          ↦ tv.(tracker.ProgressTracker.Config'))
                 (P := trk ↦ tv) (P' := trk ↦ tv) with "Htrk") as "[Hcfgf Hback1]".
    iDestruct (access_strict
                 (A := (trk.[tracker.ProgressTracker.t, "Config"]).[tracker.Config.t, "Voters"]
                         ↦ tv.(tracker.ProgressTracker.Config').(tracker.Config.Voters'))
                 (A' := (trk.[tracker.ProgressTracker.t, "Config"]).[tracker.Config.t, "Voters"]
                          ↦ tv.(tracker.ProgressTracker.Config').(tracker.Config.Voters'))
                 (P := trk.[tracker.ProgressTracker.t, "Config"]
                         ↦ tv.(tracker.ProgressTracker.Config'))
                 (P' := trk.[tracker.ProgressTracker.t, "Config"]
                          ↦ tv.(tracker.ProgressTracker.Config'))
                 with "Hcfgf") as "[Hvf Hback2]".
    wp_apply (wp_JointConfig__CommittedIndex
                (trk.[tracker.ProgressTracker.t, "Config"].[tracker.Config.t, "Voters"])
                (tv.(tracker.ProgressTracker.Config').(tracker.Config.Voters'))
                voters_ref voters
                (interface.mk_ok tracker.matchAckIndexer #(tv.(tracker.ProgressTracker.Progress')))
                (own_progress_map tv.(tracker.ProgressTracker.Progress') prs pvs)
                (pvs_acked pvs) with "[$Hidx $HP $Hvf Hvoters]").
    { iFrame "Hvoters". iPureIntro. split; first (rewrite Hvoters_dom; done). exact Hvoters_arr. }
    iIntros (N) "(Hvf & Hv & HP & %Hemp & %Hq)".
    iDestruct ("Hback2" with "Hvf") as "Hcfgf".
    iDestruct ("Hback1" with "Hcfgf") as "Htrk".
    iDestruct "Hv" as (voters') "[%Hdom Hvoters]".
    iAssert (own_tracker cfg tv (trk.mk votes prs pvs))
      with "[Hvotes HP Hvoters Hlearners HlearnersNext]" as "Hown".
    { iDestruct "HP" as "(_ & Hprogs)". rewrite /own_tracker.
      iExists voters_ref, voters', learners, learnersNext. iFrame "∗#%". iPureIntro. rewrite Hdom. exact Hvoters_dom. }
    wp_auto.
    iApply "HΦ". iFrame "Htrk Hown". rewrite Hvoters_dom in Hemp, Hq.
    iPureIntro. split; [exact Hemp | exact Hq].
  Qed.

End ProgressTrackerCommittedProof.
