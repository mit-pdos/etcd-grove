Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Inflights__reset.

Module InflightsResetProof (P : INFLIGHTS__RESET_POSTULATES) : INFLIGHTS__RESET.

  Lemma wp_Inflights__reset : wp_Inflights__reset_body.
  Proof.
    intros_ambient.
    intros l iv buf.
    wp_start as "Hin". iNamed "Hin". wp_auto. iApply "HΦ".
    rewrite /own_inflights. iFrame. iPureIntro.
    (* [start] and [count] go to [0] and the buffer is untouched, so every
       conjunct of the ring invariant is an instance of the old one *)
    destruct Hinfl_ok as (?&?&?&?&?&?).
    rewrite /inflights_ok /=. split_and!; word.
  Qed.

End InflightsResetProof.
