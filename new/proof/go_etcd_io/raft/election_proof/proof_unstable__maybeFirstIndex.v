Require Export New.proof.go_etcd_io.raft.election_proof.postulates_unstable__maybeFirstIndex.

Module UnstableMaybeFirstIndexProof (P : UNSTABLE__MAYBEFIRSTINDEX_POSTULATES) : UNSTABLE__MAYBEFIRSTINDEX.

  Lemma wp_unstable__maybeFirstIndex : wp_unstable__maybeFirstIndex_body.
  Proof.
    intros_ambient.
    intros u uv uents snap.
    wp_start as "H". iNamed "H". iNamed "Hun". wp_auto.
    destruct snap as [sid|].
    - (* a pending snapshot: [snapshot.Metadata.Index + 1] *)
      iEval (rewrite own_snap_Some) in "Hsnap". iDestruct "Hsnap" as (sv) "[#Hsv %Hmeta]".
      iDestruct (typed_pointsto_not_null with "Hsv") as %Hnn.
      rewrite (bool_decide_eq_false_2 (uv.(raft.unstable.snapshot') = null) Hnn) /=.
      wp_auto.
      iApply "HΦ". rewrite /own_unstable. iFrame. iPureIntro.
      destruct Hmeta as [Hidx _]. split.
      + first [done | rewrite (bool_decide_eq_true_2 (Some sid ≠ None)) //].
      + intros ? [= <-]. rewrite Hidx //.
    - iEval (rewrite own_snap_None) in "Hsnap". iDestruct "Hsnap" as %Hns.
      rewrite Hns (bool_decide_eq_true_2 (null = null)) //=. wp_auto.
      iApply "HΦ". rewrite /own_unstable. iFrame. iPureIntro.
      split; [first [done | rewrite (bool_decide_eq_false_2 (None ≠ None)) //]|by intros ? ?].
  Qed.

End UnstableMaybeFirstIndexProof.
