Require Export New.proof.go_etcd_io.raft.election_proof.postulates_unstable__restore.

Module UnstableRestoreProof (P : UNSTABLE__RESTORE_POSTULATES) : UNSTABLE__RESTORE.

  (** Straight-line: five field stores, the last of which installs the
      address of the parameter's own cell.  That cell is persisted, which is
      what [own_snap] holds. *)
  Lemma wp_unstable__restore : wp_unstable__restore_body.
  Proof.
    intros_ambient.
    intros u uv uents sv.
    wp_start as "H". iNamed "H". iNamed "Hun".
    iApply wp_fupd. wp_auto.
    iPersist "s". iModIntro.
    iApply "HΦ". rewrite /own_unstable. iFrame "Hu".
    iSplitL; [iSplitL; [iApply own_slice_cap_nil | iApply own_slice_nil] |].
    iSplit; last (iPureIntro; done).
    rewrite own_snap_Some. iExists sv. iFrame "s". iPureIntro. done.
  Qed.

End UnstableRestoreProof.
