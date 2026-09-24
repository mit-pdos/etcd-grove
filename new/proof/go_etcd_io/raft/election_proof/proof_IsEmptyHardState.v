Require Export New.proof.go_etcd_io.raft.election_proof.postulates_IsEmptyHardState.

Module IsEmptyHardStateProof (P : ISEMPTYHARDSTATE_POSTULATES) : ISEMPTYHARDSTATE.
Import P.

  Lemma wp_IsEmptyHardState : wp_IsEmptyHardState_body.
  Proof.
    intros_ambient.
    intros st.
    wp_start as "_".
    iDestruct (is_pkg_init_access with "[$]") as "@".
    wp_auto.
    wp_apply P.wp_isHardStateEqual.
    iApply "HΦ". destruct st. done.
  Qed.

End IsEmptyHardStateProof.
