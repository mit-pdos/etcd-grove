Require Export New.proof.go_etcd_io.raft.election_proof.postulates_pbEntryID.

Module PbEntryIDProof (P : PBENTRYID_POSTULATES) : PBENTRYID.
Import P.

  Lemma wp_pbEntryID : wp_pbEntryID_body.
  Proof.
    intros_ambient.
    intros p dq e.
    wp_start as "H". iNamed "H". wp_auto.
    iApply "HΦ". iFrame.
  Qed.

End PbEntryIDProof.
