Require Export New.proof.go_etcd_io.raft.election_proof.postulates_releasePendingReadIndexMessages.

Module ReleasePendingReadIndexMessagesProof
  (P : RELEASEPENDINGREADINDEXMESSAGES_POSTULATES)
  : RELEASEPENDINGREADINDEXMESSAGES.

  (** The length test reads [0] and the function returns. *)
  Lemma wp_releasePendingReadIndexMessages :
    wp_releasePendingReadIndexMessages_body.
  Proof.
    intros_ambient.
    intros cfg r id s.
    wp_start as "Hphys". iNamed "Hphys".
    wp_auto.
    wp_apply (wp_raft_load_pendingReadIndexMessages with "Hphys")
      as "%sl [Hphys %Hsl]".
    rewrite Hsl.
    wp_auto.
    by iApply "HΦ".
  Qed.

End ReleasePendingReadIndexMessagesProof.
