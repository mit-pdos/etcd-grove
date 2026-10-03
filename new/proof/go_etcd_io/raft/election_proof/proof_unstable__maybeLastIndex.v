Require Export New.proof.go_etcd_io.raft.election_proof.postulates_unstable__maybeLastIndex.

Module UnstableMaybeLastIndexProof (P : UNSTABLE__MAYBELASTINDEX_POSTULATES) : UNSTABLE__MAYBELASTINDEX.

  Lemma wp_unstable__maybeLastIndex : wp_unstable__maybeLastIndex_body.
  Proof.
    intros_ambient.
    intros u uv uents snap.

    intros Hnw. wp_start as "H". iNamed "H". iNamed "Hun". wp_auto.
    iDestruct (slice_len_Z with "Hents") as %Hlen.
    destruct (decide (uents = [])) as [He|Hne].
    - rewrite He in Hlen. simpl in Hlen.
      assert (uv.(raft.unstable.entries').(slice.len) = W64 0) as Hz by word.
      assert (bool_decide (uv.(raft.unstable.entries').(slice.len) = W64 0) = true)
        as Hb1 by (apply bool_decide_eq_true_2; exact Hz).
      rewrite Hb1 /=. wp_auto.
      destruct snap as [sid|].
      + (* the suffix is empty and a snapshot is pending: its index *)
        iEval (rewrite own_snap_Some) in "Hsnap". iDestruct "Hsnap" as (sv) "[#Hsv %Hmeta]".
        iDestruct (typed_pointsto_not_null with "Hsv") as %Hnn.
        rewrite (bool_decide_eq_false_2 (uv.(raft.unstable.snapshot') = null) Hnn) /=.
        wp_auto.
        iApply ("HΦ" $! _ true). rewrite /own_unstable. iFrame. iPureIntro.
        destruct Hmeta as [Hidx _].
        split; [|intros Hc; exfalso; apply Hc; exact He].
        intros _. split; [first [done | rewrite (bool_decide_eq_true_2 (Some sid ≠ None)) //]|].
        intros ? [= <-]. exact Hidx.
      + iEval (rewrite own_snap_None) in "Hsnap". iDestruct "Hsnap" as %Hns.
        assert (bool_decide (uv.(raft.unstable.snapshot') = null) = true) as Hbsnap
          by (apply bool_decide_eq_true_2; done).
        rewrite Hbsnap /=. wp_auto.
        iApply ("HΦ" $! (W64 0) false). rewrite /own_unstable. iFrame. iPureIntro.
        split; [|intros Hc; exfalso; apply Hc; exact He].
        intros _. split; [first [done | rewrite (bool_decide_eq_false_2 (None ≠ None)) //]|by intros ? ?].
    - assert (uv.(raft.unstable.entries').(slice.len) ≠ W64 0) as Hz.
      { destruct uents as [|x xs]; [done|]. intros Hc. rewrite Hc in Hlen.
        simpl in Hlen. word. }
      assert (bool_decide (uv.(raft.unstable.entries').(slice.len) = W64 0) = false)
        as Hb1 by (apply bool_decide_eq_false_2; exact Hz).
      rewrite Hb1 /=. wp_auto.
      iApply ("HΦ" $! _ true). rewrite /own_unstable. iFrame. iPureIntro.
      split; [intros Hc; exfalso; apply Hne; exact Hc | intros _; split; [done|word]].
  Qed.

End UnstableMaybeLastIndexProof.
