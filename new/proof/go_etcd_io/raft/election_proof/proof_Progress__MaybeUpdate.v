Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Progress__MaybeUpdate.

Module ProgressMaybeUpdateProof (P : PROGRESS__MAYBEUPDATE_POSTULATES)
  : PROGRESS__MAYBEUPDATE.

  Lemma wp_Progress__MaybeUpdate : wp_Progress__MaybeUpdate_body.
  Proof.
    intros_ambient.
    intros pr pv iv n.
    wp_start as "H". iNamed "H". iNamed "Hpr". wp_auto.
    rewrite /progress_maybe_update.
    destruct (decide (uint.Z n ≤ uint.Z pv.(tracker.Progress.Match'))) as [Hle|Hle].
    - (* [n <= pr.Match]: stale *)
      rewrite (bool_decide_eq_true_2 (uint.Z n ≤ _)); last done.
      wp_auto.
      rewrite bool_decide_eq_false_2; last lia.
      iApply "HΦ". rewrite /own_progress. iFrame "∗%".
    - rewrite (bool_decide_eq_false_2 (uint.Z n ≤ _)); last done.
      wp_auto.
      wp_apply wp_max2_uint64.
      rewrite (bool_decide_eq_true_2 (uint.Z pv.(tracker.Progress.Match') < uint.Z n));
        last lia.
      iApply "HΦ". rewrite /own_progress. iFrame "∗%".
  Qed.

End ProgressMaybeUpdateProof.
