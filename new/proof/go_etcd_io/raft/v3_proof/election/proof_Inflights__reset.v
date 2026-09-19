Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_Inflights__reset.

Module InflightsResetProof (P : INFLIGHTS__RESET_POSTULATES) : INFLIGHTS__RESET.

  Lemma wp_Inflights__reset : wp_Inflights__reset_body.
  Proof.
    intros_ambient.
    intros l iv.
   wp_start as "Hl". wp_auto. iApply "HΦ". iFrame.
  Qed.

End InflightsResetProof.
