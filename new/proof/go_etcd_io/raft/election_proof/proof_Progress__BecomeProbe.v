Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Progress__BecomeProbe.

Module ProgressBecomeProbeProof (P : PROGRESS__BECOMEPROBE_POSTULATES) : PROGRESS__BECOMEPROBE.
Import P.

  (** Both arms call [ResetState(StateProbe)] (exact spec), then write
      [Next]; the shared tail writes [sentCommit].  [max]/[min] are
      stepped with [wp_max2_uint64] (framework) and [wp_min2_uint64]
      ([inv_tracker.v]), whose results are [w64_max]/[w64_min] by
      definition. *)
  Lemma wp_Progress__BecomeProbe : wp_Progress__BecomeProbe_body.
  Proof.
    intros_ambient.
    intros pr pv iv.
    wp_start as "H". iNamed "H".
    iPoseProof "Hpr" as "Hpr'". iNamed "Hpr'".
    assert (progress_state_ok (W64 0)) as Hst by (by left).
    rewrite /progress_become_probe /progress_become_probe_next.
    wp_auto.
    destruct (decide (pv.(tracker.Progress.State') = W64 2)) as [Hs|Hs].
    - (* [StateSnapshot]: probe from past the pending snapshot *)
      rewrite Hs. wp_auto.
      iAssert (own_progress pr pv iv) with "[Hpv Hinfl]" as "Hpr".
      { rewrite /own_progress. iFrame "∗%". }
      wp_apply (wp_Progress__ResetState _ _ _ _ Hst with "[$Hpr]"). iIntros "Hpr".
      iNamed "Hpr". wp_auto.
      wp_apply wp_max2_uint64.
      wp_apply wp_min2_uint64.
      iApply "HΦ". rewrite /own_progress. iFrame "Hpv Hinfl". iPureIntro.
      split; [exact Hnolearner | exact Hst].
    - (* any other state: probe from [Match + 1] *)
      rewrite bool_decide_eq_false_2; last done.
      wp_auto.
      iAssert (own_progress pr pv iv) with "[Hpv Hinfl]" as "Hpr".
      { rewrite /own_progress. iFrame "∗%". }
      wp_apply (wp_Progress__ResetState _ _ _ _ Hst with "[$Hpr]"). iIntros "Hpr".
      iNamed "Hpr". wp_auto.
      wp_apply wp_min2_uint64.
      iApply "HΦ". rewrite /own_progress. iFrame "Hpv Hinfl". iPureIntro.
      split; [exact Hnolearner | exact Hst].
  Qed.

End ProgressBecomeProbeProof.
