Require Export New.proof.go_etcd_io.raft.election_proof.postulates_unstable__maybeTerm.

Module UnstableMaybeTermProof (P : UNSTABLE__MAYBETERM_POSTULATES) : UNSTABLE__MAYBETERM.
Import P.

  Lemma wp_unstable__maybeTerm : wp_unstable__maybeTerm_body.
  Proof.
    intros_ambient.
    intros u uv uents snap i.

    intros Hsoff Hnw. wp_start as "H". iNamed "H". iNamed "Hun". wp_auto.
    iDestruct (own_slice_len with "Hents") as %[Hlen Hlen2].
    destruct (decide (uint.Z i < uint.Z uv.(raft.unstable.offset'))%Z) as [Hlt|Hge].
    - assert (bool_decide (uint.Z i < uint.Z uv.(raft.unstable.offset'))%Z = true)
        as Hb1 by (apply bool_decide_eq_true_2; done).
      rewrite Hb1 /=. wp_auto.
      destruct snap as [sid|].
      + (* below [offset], with a snapshot pending: its term at its index *)
        iEval (rewrite own_snap_Some) in "Hsnap". iDestruct "Hsnap" as (sv) "[#Hsv %Hmeta]".
        iDestruct (typed_pointsto_not_null with "Hsv") as %Hnn.
        destruct Hmeta as [Hidx Htm].
        rewrite (bool_decide_eq_false_2 (uv.(raft.unstable.snapshot') = null) Hnn) /=.
        wp_auto.
        rewrite Hidx.
        destruct (decide (sid.(raft.entryID.index') = i)) as [Hi|Hi].
        * rewrite (bool_decide_eq_true_2 _ Hi) /=. wp_auto.
          iApply ("HΦ" $! _ true). rewrite /own_unstable. iFrame. iPureIntro.
          split; [split; [intros _; right; by exists sid | done] |].
          intros _. right. exists sid. split_and!; [done|done|exact Htm].
        * rewrite (bool_decide_eq_false_2 _ Hi) /=. wp_auto.
          iApply ("HΦ" $! (W64 0) false). rewrite /own_unstable. iFrame. iPureIntro.
          split; [split; [done|] | intros Hf; discriminate Hf].
          intros [Hc|(sid' & [= <-] & ->)]; [lia|done].
      + iEval (rewrite own_snap_None) in "Hsnap". iDestruct "Hsnap" as %Hns.
        assert (bool_decide (uv.(raft.unstable.snapshot') = null) = true) as Hbsnap
          by (apply bool_decide_eq_true_2; done).
        rewrite Hbsnap /=. wp_auto.
        iApply ("HΦ" $! (W64 0) false). rewrite /own_unstable. iFrame. iPureIntro.
        split; [split; [done|] | intros Hf; discriminate Hf].
        intros [Hc|(sid' & Hc & _)]; [lia|discriminate Hc].
    - assert (bool_decide (uint.Z i < uint.Z uv.(raft.unstable.offset'))%Z = false)
        as Hb1 by (apply bool_decide_eq_false_2; done).
      rewrite Hb1 /=. wp_auto.
      (* at or above [offset], a pending snapshot's index is not [i] *)
      assert (Hnsnap : ¬ ∃ sid, snap = Some sid ∧ i = sid.(raft.entryID.index')).
      { intros (sid & Hs & ->). specialize (Hsoff sid Hs). lia. }
      wp_apply (wp_unstable__maybeLastIndex _ _ _ snap Hnw with "[Hu Hents Hents_cap]")
        as "%last %ok (Hun & %Hok1 & %Hok2)".
      { rewrite /own_unstable. iFrame "∗#". }
      iNamed "Hun".
      destruct (decide (uents = [])) as [He|Hne].
      + destruct (Hok1 He) as [Hok Hlast]. subst ok.
        destruct snap as [sid|].
        * (* only the snapshot: [last] is its index, below [i] *)
          rewrite bool_decide_eq_true_2 /=; last done.
          rewrite (Hlast sid eq_refl). wp_auto.
          specialize (Hsoff sid eq_refl).
          rewrite bool_decide_eq_true_2; last lia. wp_auto.
          iApply ("HΦ" $! (W64 0) false). rewrite /own_unstable. iFrame. iPureIntro.
          rewrite He /=. split; [split; [done|] | intros Hf; discriminate Hf].
          intros [Hc|Hc]; [lia|by destruct (Hnsnap Hc)].
        * rewrite bool_decide_eq_false_2 /=; last (by intros ?). wp_auto.
          iApply ("HΦ" $! (W64 0) false). rewrite /own_unstable. iFrame. iPureIntro.
          rewrite He /=. split; [split; [done|] | intros Hf; discriminate Hf].
          intros [Hc|Hc]; [lia|by destruct (Hnsnap Hc)].
      + destruct (Hok2 Hne) as [Hokt Hlast]. rewrite Hokt /=. wp_auto.
        destruct (decide (uint.Z last < uint.Z i)%Z) as [Hgt|Hle].
        * assert (bool_decide (uint.Z last < uint.Z i)%Z = true) as Hb2
            by (apply bool_decide_eq_true_2; exact Hgt).
          rewrite Hb2 /=. wp_auto.
          iApply ("HΦ" $! (W64 0) false). rewrite /own_unstable. iFrame. iPureIntro.
          split; [split; [done|] | intros Hf; discriminate Hf].
          intros [Hc|Hc]; [lia|by destruct (Hnsnap Hc)].
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
          iApply ("HΦ" $! e.(raftpb.Entry.Term') true). rewrite /own_unstable. iFrame. iPureIntro.
          split; [split; [intros _; left; lia | done] |].
          intros _. left. split; [lia|]. exists e. split; [|done].
          replace (Z.to_nat (uint.Z i - uint.Z uv.(raft.unstable.offset')))
            with (Z.to_nat (sint.Z (word.sub i uv.(raft.unstable.offset')))) by word.
          exact He_lk.
  Qed.

End UnstableMaybeTermProof.
