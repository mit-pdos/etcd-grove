Require Export New.proof.go_etcd_io.raft.election_proof.postulates_ProgressTracker__Committed.

Module ProgressTrackerCommittedProof (P : PROGRESSTRACKER__COMMITTED_POSTULATES)
  : PROGRESSTRACKER__COMMITTED.
Import P.

  (** Load [p.Progress], convert it to the interface (a pure step), and
      hand everything to [JointConfig.CommittedIndex]. *)
  Lemma wp_ProgressTracker__Committed : wp_ProgressTracker__Committed_body.
  Proof.
    intros_ambient.
    intros cfg trk tv t.
    wp_start as "(Htrk & Hown)".
    wp_auto.
    (* [is_pkg_init tracker] is in the persistent context, which a
       [$]-frame pattern does not consult *)
    wp_apply (wp_JointConfig__CommittedIndex with "[$Htrk $Hown]").
    { iAssumption. }
    iIntros (N) "(Htrk & Hown & %Hemp & %Hq)".
    wp_auto. iApply "HΦ". by iFrame.
  Qed.

End ProgressTrackerCommittedProof.
