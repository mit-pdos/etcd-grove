Require Export New.proof.go_etcd_io.raft.election_proof.postulates_unstable__maybeLastIndex.

Module UnstableMaybeLastIndexProof (P : UNSTABLE__MAYBELASTINDEX_POSTULATES) : UNSTABLE__MAYBELASTINDEX.

  Lemma wp_unstable__maybeLastIndex : wp_unstable__maybeLastIndex_body.
  Proof.
    intros_ambient.
    intros u uv uents.

    intros Hns Hnw. wp_start as "H". iNamed "H". wp_auto.
    iDestruct (slice_len_Z with "Hents") as %Hlen.
    assert (bool_decide (uv.(raft.unstable.snapshot') = null) = true) as Hbsnap
      by (apply bool_decide_eq_true_2; done).
    destruct (decide (uents = [])) as [He|Hne].
    - rewrite He in Hlen. simpl in Hlen.
      assert (uv.(raft.unstable.entries').(slice.len) = W64 0) as Hz by word.
      assert (bool_decide (uv.(raft.unstable.entries').(slice.len) = W64 0) = true)
        as Hb1 by (apply bool_decide_eq_true_2; exact Hz).
      rewrite Hb1 /=. wp_auto.
      rewrite Hbsnap /=. wp_auto.
      iApply ("HΦ" $! (W64 0) false). iFrame. iPureIntro.
      split; [done | intros Hc; exfalso; apply Hc; exact He].
    - assert (uv.(raft.unstable.entries').(slice.len) ≠ W64 0) as Hz.
      { destruct uents as [|x xs]; [done|]. intros Hc. rewrite Hc in Hlen.
        simpl in Hlen. word. }
      assert (bool_decide (uv.(raft.unstable.entries').(slice.len) = W64 0) = false)
        as Hb1 by (apply bool_decide_eq_false_2; exact Hz).
      rewrite Hb1 /=. wp_auto.
      iApply ("HΦ" $! _ true). iFrame. iPureIntro.
      split; [intros Hc; exfalso; apply Hne; exact Hc | intros _; split; [done|word]].
  Qed.

End UnstableMaybeLastIndexProof.
