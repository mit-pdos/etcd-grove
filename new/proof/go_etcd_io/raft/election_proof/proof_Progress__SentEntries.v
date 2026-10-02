Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Progress__SentEntries.

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
    intros pr p entries bytes Hnotsnap Hnotfull.
    wp_start as "H". iNamed "H". iNamed "Hpr".
    pose proof Habs as Habs0.
    apply progress_abs_Some in Habs0 as (Hl & Hst & _).
    wp_auto.
    rewrite /progress_sent_entries.
    (* the record's state is Probe or Replicate -- the premise excludes
       Snapshot -- so the [panic] arm is unreachable. *)
    destruct (p.(progress.state)) eqn:Hps; last (exfalso; by apply Hnotsnap); rewrite Hst; cbn [prstate_w64].
    - (* StateProbe: the switch falls through to the second arm *)
      case_bool_decide as Hb1; first (w64_absurd Hb1).
      (* [wp_auto] runs the rest of the switch itself *)
      wp_auto.
      case_bool_decide as Hgt.
      + rewrite decide_True //. wp_auto.
        iApply "HΦ". iExists _. iFrame "Hpv Hinfl". iPureIntro.
        progress_abs_from Habs.
      + rewrite decide_False //. wp_auto.
        iApply "HΦ". iExists _. iFrame "Hpv Hinfl". iPureIntro.
        progress_abs_from Habs.
    - (* StateReplicate *)
      case_bool_decide as Hb1; last (exfalso; by apply Hb1).
      wp_auto.
      case_bool_decide as Hgt.
      + (* entries > 0: [Next] moves and the window records the batch.  The
           [Add] is legal because the caller promised the window is not
           full -- see the spec. *)
        rewrite decide_True //.
        wp_auto.
        wp_apply (wp_Inflights__Add with "[$Hinfl]") as "Hinfl".
        { by apply Hnotfull. }
        wp_apply (wp_Inflights__Full with "[$Hinfl]") as "Hinfl".
        try wp_auto.
        iApply "HΦ". iExists _. iFrame "Hpv Hinfl". iPureIntro.
        progress_abs_from Habs.
      + rewrite decide_False //.
        wp_auto.
        wp_apply (wp_Inflights__Full with "[$Hinfl]") as "Hinfl".
        try wp_auto.
        iApply "HΦ". iExists _. iFrame "Hpv Hinfl". iPureIntro.
        progress_abs_from Habs.
  Qed.

End ProgressSentEntriesProof.
