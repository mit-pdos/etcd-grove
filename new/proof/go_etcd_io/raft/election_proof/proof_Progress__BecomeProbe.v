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
    intros pr p.
    wp_start as "H". iNamed "H". iNamed "Hpr".
    pose proof Habs as Habs0.
    apply progress_abs_Some in Habs0 as (Hl & Hst & Hm & Hn & Hsc & Hps & _).
    rewrite /progress_become_probe /progress_become_probe_next.
    wp_auto.
    destruct (decide (p.(progress.state) = prstate.Snapshot)) as [Hs|Hs].
    - (* [StateSnapshot]: probe from past the pending snapshot *)
      assert (pv.(tracker.Progress.State') = W64 2) as Hs2 by rewrite Hst Hs //.
      rewrite Hs2. wp_auto.
      iDestruct (own_Progress_intro _ _ p with "Hpv Hinfl [//]") as "Hpr". clear Habs.
      wp_apply (wp_Progress__ResetState _ _ prstate.Probe with "[$Hpr]") as "Hpr".
      iNamed "Hpr". wp_auto.
      wp_apply wp_max2_uint64.
      wp_apply wp_min2_uint64.
      iApply "HΦ". iExists _. iFrame "Hpv Hinfl". iPureIntro.
      progress_abs_from Habs.
    - (* any other state: probe from [Match + 1] *)
      rewrite bool_decide_eq_false_2;
        last (rewrite Hst; intros Hc; apply Hs, prstate_w64_inj; exact Hc).
      wp_auto.
      iDestruct (own_Progress_intro _ _ p with "Hpv Hinfl [//]") as "Hpr". clear Habs.
      wp_apply (wp_Progress__ResetState _ _ prstate.Probe with "[$Hpr]") as "Hpr".
      iNamed "Hpr". wp_auto.
      wp_apply wp_min2_uint64.
      iApply "HΦ". iExists _. iFrame "Hpv Hinfl". iPureIntro.
      progress_abs_from Habs.
  Qed.

End ProgressBecomeProbeProof.
