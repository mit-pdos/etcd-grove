Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Progress__IsPaused.

(** Discharge [False] from an equation between two distinct [w64]
    literals.  [word] cannot: it reports "Cannot find witness". *)
Ltac w64_absurd H :=
  exfalso; apply (f_equal uint.Z) in H; vm_compute in H; discriminate.

Module ProgressIsPausedProof (P : PROGRESS__ISPAUSED_POSTULATES) : PROGRESS__ISPAUSED.

  (** The three-armed switch; the [panic] arm is ruled out by the record's
      state being one of the three ([progress_abs], [defs.v]). *)
  Lemma wp_Progress__IsPaused : wp_Progress__IsPaused_body.
  Proof.
    intros_ambient.
    intros pr p.
    wp_start as "H". iNamed "H". iNamed "Hpr".
    progress_open Habs p. wp_auto.
    rewrite /progress_is_paused /=.
    destruct st; rewrite Hst; cbn [prstate_w64].
    - (* StateProbe *)
      case_bool_decide as Hb; last (exfalso; by apply Hb).
      wp_auto. iApply "HΦ". iExists _. iFrame "Hpv Hinfl". iPureIntro.
      progress_abs_solve.
    - (* StateReplicate *)
      case_bool_decide as Hb1; first (w64_absurd Hb1).
      (* [wp_auto] runs the rest of the switch: the remaining tests are
         between closed [w64] literals and it discharges them itself. *)
      wp_auto. iApply "HΦ". iExists _. iFrame "Hpv Hinfl". iPureIntro.
      progress_abs_solve.
    - (* StateSnapshot: paused unconditionally *)
      case_bool_decide as Hb1; first (w64_absurd Hb1).
      wp_auto. iApply "HΦ". iExists _. iFrame "Hpv Hinfl". iPureIntro.
      progress_abs_solve.
  Qed.
End ProgressIsPausedProof.
