Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_Progress__SentEntries.

(** Discharge [False] from an equation between two distinct [w64]
    literals.  [word] cannot: it reports "Cannot find witness". *)
Ltac w64_absurd H :=
  exfalso; apply (f_equal uint.Z) in H; vm_compute in H; discriminate.

Module ProgressSentEntriesProof (P : PROGRESS__SENTENTRIES_POSTULATES)
  : PROGRESS__SENTENTRIES.
Import P.

  Lemma wp_Progress__SentEntries : wp_Progress__SentEntries_body.
  Proof.
    intros_ambient.
    intros pr pv iv entries bytes Hnotsnap Hnotfull.
    wp_start as "H". iNamed "H". iNamed "Hpr". wp_auto.
    (* [progress_state_ok] plus the premise leaves Probe and Replicate, so
       the [panic] arm is unreachable. *)
    destruct Hstate_ok as [Hs | [Hs | Hs]]; last congruence; rewrite Hs.
    - (* StateProbe: the switch falls through to the second arm *)
      case_bool_decide as Hb1; first (w64_absurd Hb1).
      (* [wp_auto] runs the rest of the switch itself *)
      wp_auto.
      case_bool_decide as Hgt.
      + wp_auto.
        iApply "HΦ". rewrite /own_progress /own_progress_at.
        iExists _, iv. iFrame "Hpv Hinfl". iPureIntro. split; [done|].
        rewrite /progress_state_ok /=. by left.
      + wp_auto.
        iApply "HΦ". rewrite /own_progress /own_progress_at.
        iExists _, iv. iFrame "Hpv Hinfl". iPureIntro. split; [done|].
        rewrite /progress_state_ok /=. by left.
    - (* StateReplicate *)
      case_bool_decide as Hb1; last (exfalso; by apply Hb1).
      wp_auto.
      case_bool_decide as Hgt.
      + (* entries > 0: [Next] moves and the window records the batch.  The
           [Add] is legal because the caller promised the window is not
           full -- see the spec. *)
        wp_auto.
        wp_apply (wp_Inflights__Add with "[$Hinfl]") as "Hinfl".
        { by apply Hnotfull. }
        iDestruct "Hinfl" as (iv') "Hinfl".
        wp_apply (wp_Inflights__Full with "[$Hinfl]") as "Hinfl".
        try wp_auto.
        iApply "HΦ". rewrite /own_progress /own_progress_at.
        iExists _, iv'. iFrame "Hpv Hinfl". iPureIntro. split; [done|].
        rewrite /progress_state_ok /=. by right; left.
      + wp_auto.
        wp_apply (wp_Inflights__Full with "[$Hinfl]") as "Hinfl".
        try wp_auto.
        iApply "HΦ". rewrite /own_progress /own_progress_at.
        iExists _, iv. iFrame "Hpv Hinfl". iPureIntro. split; [done|].
        rewrite /progress_state_ok /=. by right; left.
  Qed.

End ProgressSentEntriesProof.
