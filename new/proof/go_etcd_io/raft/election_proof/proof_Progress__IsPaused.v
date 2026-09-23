Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Progress__IsPaused.

(** Discharge [False] from an equation between two distinct [w64]
    literals.  [word] cannot: it reports "Cannot find witness". *)
Ltac w64_absurd H :=
  exfalso; apply (f_equal uint.Z) in H; vm_compute in H; discriminate.

Module ProgressIsPausedProof (P : PROGRESS__ISPAUSED_POSTULATES) : PROGRESS__ISPAUSED.

  (** The three-armed switch, plus the [panic] arm that [progress_state_ok]
      ([inv_tracker.v]) rules out.  [Hstate_ok] is [pose proof]d rather than
      destructed so that it is still around for the re-seal. *)
  Lemma wp_Progress__IsPaused : wp_Progress__IsPaused_body.
  Proof.
    intros_ambient.
    intros pr pv iv.
    wp_start as "H". iNamed "H". iNamed "Hpr". wp_auto.
    rewrite /progress_paused.
    pose proof Hstate_ok as Hs3. destruct Hs3 as [Hs|[Hs|Hs]]; rewrite Hs.
    - (* StateProbe *)
      case_decide as Hd; first (w64_absurd Hd).
      case_bool_decide as Hb; last (exfalso; by apply Hb).
      wp_auto. iApply "HΦ". rewrite /own_progress. iFrame "∗%".
    - (* StateReplicate *)
      case_decide as Hd; first (w64_absurd Hd).
      case_bool_decide as Hb1; first (w64_absurd Hb1).
      (* [wp_auto] runs the rest of the switch: the remaining tests are
         between closed [w64] literals and it discharges them itself. *)
      wp_auto. iApply "HΦ". rewrite /own_progress. iFrame "∗%".
    - (* StateSnapshot: paused unconditionally *)
      case_decide as Hd; last (exfalso; by apply Hd).
      case_bool_decide as Hb1; first (w64_absurd Hb1).
      wp_auto. iApply "HΦ". rewrite /own_progress. iFrame "∗%".
  Qed.

End ProgressIsPausedProof.
