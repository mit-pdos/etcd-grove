Require Export New.proof.go_etcd_io.raft.election_proof.postulates_readOnly__heartbeatCtx.

Module ReadOnlyHeartbeatCtxProof (P : READONLY__HEARTBEATCTX_POSTULATES)
  : READONLY__HEARTBEATCTX.

  (** [own_read_only] holds [unconfirmedReads ↦* []], so the length test
      succeeds and the function returns [nil] at once. *)
  Lemma wp_readOnly__heartbeatCtx : wp_readOnly__heartbeatCtx_body.
  Proof.
    intros_ambient.
    intros ro.
    wp_start as "Hown". iNamed "Hown". iNamed "Hown".
    iDestruct (own_slice_len with "Hucr") as %[Hl Hl0].
    wp_auto.
    rewrite bool_decide_eq_true_2; last (simpl in Hl; word).
    wp_auto.
    iApply "HΦ". rewrite /own_read_only. iFrame.
  Qed.

End ReadOnlyHeartbeatCtxProof.
