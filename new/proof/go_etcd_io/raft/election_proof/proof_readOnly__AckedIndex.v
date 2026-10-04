Require Export New.proof.go_etcd_io.raft.election_proof.postulates_readOnly__AckedIndex.

Module ReadOnlyAckedIndexProof (P : READONLY__ACKEDINDEX_POSTULATES)
  : READONLY__ACKEDINDEX.

  (** One map lookup. *)
  Lemma wp_readOnly__AckedIndex : wp_readOnly__AckedIndex_body.
  Proof.
    intros_ambient.
    intros ro r voterID.
    wp_start as "Hown". iNamed "Hown". iNamed "Hown".
    wp_auto.
    wp_apply (wp_map_lookup2 with "Hacks") as "Hacks".
    iApply "HΦ".
    iExists rov, ptrs. iFrame. done.
  Qed.

End ReadOnlyAckedIndexProof.
