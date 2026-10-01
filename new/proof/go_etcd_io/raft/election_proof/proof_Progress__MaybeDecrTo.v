Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Progress__MaybeDecrTo.

Module ProgressMaybeDecrToProof (P : PROGRESS__MAYBEDECRTO_POSTULATES)
  : PROGRESS__MAYBEDECRTO.

  Lemma wp_Progress__MaybeDecrTo : wp_Progress__MaybeDecrTo_body.
  Proof.
    intros_ambient.
    intros pr pv iv rejected matchHint.
    wp_start as "H". iNamed "H". iNamed "Hpr". wp_auto.
    rewrite /progress_maybe_decr_to.
    destruct (decide (pv.(tracker.Progress.State') = W64 1)) as [Hs|Hs].
    - rewrite (bool_decide_eq_true_2 (pv.(tracker.Progress.State') = W64 1)); last done.
      wp_auto.
      destruct (decide (uint.Z rejected ≤ uint.Z pv.(tracker.Progress.Match'))) as [Hle|Hle].
      + (* exit 1 *)
        rewrite bool_decide_eq_true_2; last done.
        wp_auto. iApply "HΦ". rewrite /own_progress. iFrame "∗%".
      + (* exit 2 *)
        rewrite bool_decide_eq_false_2; last done.
        wp_auto.
        wp_apply wp_min2_uint64.
        iApply "HΦ". rewrite /own_progress. iFrame "∗%".
    - rewrite (bool_decide_eq_false_2 (pv.(tracker.Progress.State') = W64 1)); last done.
      wp_auto.
      destruct (decide (word.sub pv.(tracker.Progress.Next') (W64 1) = rejected)) as [Hn|Hn].
      + (* exit 4: a genuine rejection while probing *)
        rewrite bool_decide_eq_true_2; last done.
        wp_auto.
        wp_apply wp_min2_uint64.
        wp_apply wp_max2_uint64.
        wp_apply wp_min2_uint64.
        iApply "HΦ". rewrite /own_progress. iFrame "∗%".
      + (* exit 3: stale *)
        rewrite bool_decide_eq_false_2; last done.
        wp_auto. iApply "HΦ". rewrite /own_progress. iFrame "∗%".
  Qed.

End ProgressMaybeDecrToProof.
