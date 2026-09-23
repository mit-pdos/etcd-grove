Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Inflights__Full.

Module InflightsFullProof (P : INFLIGHTS__FULL_POSTULATES) : INFLIGHTS__FULL.

  Lemma wp_Inflights__Full : wp_Inflights__Full_body.
  Proof.
    intros_ambient.
    intros l iv buf.
    wp_start as "H". iNamed "H". iNamed "Hin". wp_auto.
    rewrite /inflights_full.
    wp_if_destruct.
    { (* count = size: the answer is [true || _] *)
      iApply "HΦ". rewrite /own_inflights. iFrame "∗%". }
    (* [case_bool_decide] picks the [bool_decide (maxBytes ≠ 0)] in the
       postcondition, not the program's [bool_decide (maxBytes = 0)]; the
       second one is rewritten by hand. *)
    case_bool_decide as Hmb.
    - (* maxBytes ≠ 0: the byte comparison decides *)
      rewrite (bool_decide_eq_false_2
                 (iv.(tracker.Inflights.maxBytes') = W64 0) Hmb) /=.
      wp_auto. iApply "HΦ". rewrite /own_inflights. iFrame "∗%".
    - (* maxBytes = 0: the byte test is skipped *)
      rewrite (bool_decide_eq_true_2
                 (iv.(tracker.Inflights.maxBytes') = W64 0) Hmb) /=.
      wp_auto. iApply "HΦ". rewrite /own_inflights. iFrame "∗%".
  Qed.

End InflightsFullProof.
