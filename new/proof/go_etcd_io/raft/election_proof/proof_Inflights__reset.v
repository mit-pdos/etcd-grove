Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Inflights__reset.

Module InflightsResetProof (P : INFLIGHTS__RESET_POSTULATES) : INFLIGHTS__RESET.

  Lemma wp_Inflights__reset : wp_Inflights__reset_body.
  Proof.
    intros_ambient.
    intros l i.
    wp_start as "Hin". iNamed "Hin". iNamed "Hin". wp_auto. iApply "HΦ".
    iExists (iv <| tracker.Inflights.start' := W64 0 |>
                <| tracker.Inflights.count' := W64 0 |>
                <| tracker.Inflights.bytes' := W64 0 |>), buf. iSplitL.
    { rewrite /own_inflights. iFrame. iPureIntro.
      (* [start] and [count] go to [0] and the buffer is untouched, so every
         conjunct of the ring invariant is an instance of the old one *)
      destruct Hinfl_ok as (?&?&?&?&?&?).
      rewrite /inflights_ok /=. split_and!; word. }
    iPureIntro. subst i. rewrite /inflights_abs /inflights_reset /=. f_equal; word.
  Qed.

End InflightsResetProof.
