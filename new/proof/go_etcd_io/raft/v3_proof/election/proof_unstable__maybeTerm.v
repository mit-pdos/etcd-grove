Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_unstable__maybeTerm.

Module UnstableMaybeTermProof (P : UNSTABLE__MAYBETERM_POSTULATES) : UNSTABLE__MAYBETERM.
Import P.

  Lemma wp_unstable__maybeTerm : wp_unstable__maybeTerm_body.
  Proof.
    intros_ambient.
    intros u uv uents i.

    intros Hns Hnw. wp_start as "H". iNamed "H". wp_auto.
    iDestruct (own_slice_len with "Hents") as %[Hlen Hlen2].
    assert (bool_decide (uv.(raft.unstable.snapshot') = null) = true) as Hbsnap
      by (apply bool_decide_eq_true_2; done).
    destruct (decide (uint.Z i < uint.Z uv.(raft.unstable.offset'))%Z) as [Hlt|Hge].
    - assert (bool_decide (uint.Z i < uint.Z uv.(raft.unstable.offset'))%Z = true)
        as Hb1 by (apply bool_decide_eq_true_2; done).
      rewrite Hb1 /=. wp_auto.
      rewrite Hbsnap /=. wp_auto.
      iApply ("HΦ" $! (W64 0) false). iFrame. iPureIntro.
      split; [done | lia].
    - assert (bool_decide (uint.Z i < uint.Z uv.(raft.unstable.offset'))%Z = false)
        as Hb1 by (apply bool_decide_eq_false_2; done).
      rewrite Hb1 /=. wp_auto.
      wp_apply (wp_unstable__maybeLastIndex _ _ _ Hns Hnw with "[$Hu $Hents]")
        as "%last %ok (Hu & Hents & %Hok1 & %Hok2)".
      destruct (decide (uents = [])) as [He|Hne].
      + rewrite (Hok1 He) /=. wp_auto.
        iApply ("HΦ" $! (W64 0) false). iFrame. iPureIntro.
        rewrite He /=. split; [done | lia].
      + destruct (Hok2 Hne) as [Hokt Hlast]. rewrite Hokt /=. wp_auto.
        destruct (decide (uint.Z last < uint.Z i)%Z) as [Hgt|Hle].
        * assert (bool_decide (uint.Z last < uint.Z i)%Z = true) as Hb2
            by (apply bool_decide_eq_true_2; exact Hgt).
          rewrite Hb2 /=. wp_auto.
          iApply ("HΦ" $! (W64 0) false). iFrame. iPureIntro.
          split; [done | lia].
        * assert (bool_decide (uint.Z last < uint.Z i)%Z = false) as Hb2
            by (apply bool_decide_eq_false_2; exact Hle).
          rewrite Hb2 /=. wp_auto.
          assert (0 ≤ sint.Z (word.sub i uv.(raft.unstable.offset')) <
                  sint.Z uv.(raft.unstable.entries').(slice.len))%Z as Hbnd by word.
          rewrite decide_True //.
          destruct (uents !! Z.to_nat (sint.Z (word.sub i uv.(raft.unstable.offset'))))
            as [e|] eqn:He_lk; last first.
          { exfalso. apply lookup_ge_None_1 in He_lk. word. }
          iDestruct (own_slice_elem_acc
                       (sint.Z (word.sub i uv.(raft.unstable.offset')))
                       with "Hents") as "[He Hback]"; [word | exact He_lk | ].
          wp_auto.
          iDestruct ("Hback" with "He") as "Hents".
          rewrite (list_insert_id _ _ _ He_lk).
          iApply ("HΦ" $! e.(raftpb.Entry.Term') true). iFrame. iPureIntro.
          split; [intros _; lia | done].
  Qed.

End UnstableMaybeTermProof.
