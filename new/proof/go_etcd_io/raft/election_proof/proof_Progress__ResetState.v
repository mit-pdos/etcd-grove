Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Progress__ResetState.

Module ProgressResetStateProof (P : PROGRESS__RESETSTATE_POSTULATES) : PROGRESS__RESETSTATE.
Import P.

  Lemma wp_Progress__ResetState : wp_Progress__ResetState_body.
  Proof.
    intros_ambient.
    intros pr pv iv st.

    wp_start as "[Hpv Hiv]". wp_auto.
    wp_apply (wp_Inflights__reset with "[$Hiv]") as "Hiv".
    iApply "HΦ". iFrame.
  Qed.

End ProgressResetStateProof.
