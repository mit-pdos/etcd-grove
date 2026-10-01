Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Progress__CanBumpCommit.

Module ProgressCanBumpCommitProof (P : PROGRESS__CANBUMPCOMMIT_POSTULATES)
  : PROGRESS__CANBUMPCOMMIT.

  (** Goose's [&&] short-circuits, so the second comparison is only
      evaluated when the first holds; each arm is one [bool_decide]. *)
  Lemma wp_Progress__CanBumpCommit : wp_Progress__CanBumpCommit_body.
  Proof.
    intros_ambient.
    intros pr pv iv index.
    wp_start as "H". iNamed "H". iNamed "Hpr". wp_auto.
    destruct (decide (uint.Z pv.(tracker.Progress.sentCommit') < uint.Z index)) as [H1|H1].
    - rewrite (bool_decide_eq_true_2 (uint.Z pv.(tracker.Progress.sentCommit') < uint.Z index));
        last done.
      wp_auto.
      rewrite bool_decide_and (bool_decide_eq_true_2 (_ < uint.Z index)) //=.
      iApply "HΦ". rewrite /own_progress. iFrame "∗%".
    - rewrite (bool_decide_eq_false_2 (uint.Z pv.(tracker.Progress.sentCommit') < uint.Z index));
        last done.
      rewrite bool_decide_eq_false_2; last tauto.
      wp_auto. iApply "HΦ". rewrite /own_progress. iFrame "∗%".
  Qed.

End ProgressCanBumpCommitProof.
