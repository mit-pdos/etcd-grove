Require Export New.proof.go_etcd_io.raft.election_proof.postulates_IsEmptySnap.

Module IsEmptySnapProof (P : ISEMPTYSNAP_POSTULATES) : ISEMPTYSNAP.

  Lemma wp_IsEmptySnap : wp_IsEmptySnap_body.
  Proof.
    intros_ambient.
    intros sp.
    wp_start as "_". wp_auto.
    by iApply "HΦ".
  Qed.

End IsEmptySnapProof.
