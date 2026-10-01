Require Export New.proof.go_etcd_io.raft.election_proof.postulates_pbEntryID.

Module PbEntryIDProof (P : PBENTRYID_POSTULATES) : PBENTRYID.

  Lemma wp_pbEntryID : wp_pbEntryID_body.
  Proof.
    intros_ambient.
    intros p dq e.
    wp_start as "He". wp_auto.
    iApply "HΦ". iFrame.
  Qed.

End PbEntryIDProof.
