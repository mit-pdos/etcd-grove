Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_limitSize.

Module LimitSizeProof (P : LIMITSIZE_POSTULATES) : LIMITSIZE.
Import P.

  (** Three exits, each giving a different [n]:
      - [len(ents) == 0]: the input comes straight back.  [es = []], so
        [take 0 es = es] and any [n] would do; [0] is chosen.
      - the loop's early [return ents[:limit]]: a two-index sub-slice, so
        [n = limit] and the page is [own_slice_split_all]'s left half, with
        the right half captured in the wand's closure.  This is the only
        [return] out of a [for:] body on the log path: [wp_auto] first
        turns [return: v] into [return_val v], and only then does
        [wp_for_post] see a [for_postcondition] and pick
        [wp_for_post_return].
      - falling out of the loop: [n = |es|], the input again.

      The loop invariant is just the two mutable locations plus
      [1 <= limit <= |es|]; nothing about [size], since the spec says
      nothing about where the cut falls.  [Entry.Size] has a pointer
      receiver applied to [&ents[i]], not to a loaded value, so the element
      pointsto comes from [own_slice_elem_acc] and goes back with
      [list_insert_id]. *)
  Lemma wp_limitSize : wp_limitSize_body.
  Proof.
    intros_ambient.
    intros s es dq maxSize.
    wp_start as "H". iNamed "H". wp_auto.
    iDestruct (own_slice_len with "Hs") as %[Hlen Hlen'].
    iDestruct (own_slice_wf with "Hs") as %Hwf.
    wp_if_destruct.
    { assert (es = []) as -> by (apply nil_length_inv; word).
      iApply ("HΦ" $! s 0%nat). rewrite take_0. iFrame.
      iSplit.
      - iPureIntro. split; [lia | congruence].
      - iIntros "H". iFrame. }
    assert (0 < length es)%nat as Hne by word.
    assert (∃ e0, es !! 0%nat = Some e0) as [e0 He0]
      by (apply lookup_lt_is_Some_2; lia).
    rewrite decide_True; last word.
    iDestruct (own_slice_elem_acc 0 e0 with "Hs") as "[He Hsback]"; [lia|done|].
    wp_auto.
    wp_apply (wp_Entry__Size with "[$He]") as "%sz0 He".
    iDestruct ("Hsback" with "He") as "Hs".
    rewrite list_insert_id //.
    iAssert (∃ (lim sz : w64),
      "limit" ∷ limit_ptr ↦ lim ∗
      "size" ∷ size_ptr ↦ sz ∗
      "%Hlim" ∷ ⌜ (1 ≤ sint.Z lim ≤ Z.of_nat (length es))%Z ⌝)%I
      with "[limit size]" as "IH".
    { iFrame. iPureIntro. word. }
    wp_for "IH".
    wp_if_destruct.
    - assert (∃ e, es !! Z.to_nat (sint.Z lim) = Some e) as [e He]
        by (apply lookup_lt_is_Some_2; word).
      rewrite decide_True; last word.
      iDestruct (own_slice_elem_acc (sint.Z lim) e with "Hs") as "[He Hsback]";
        [word|done|].
      wp_auto.
      wp_apply (wp_Entry__Size with "[$He]") as "%szi He".
      iDestruct ("Hsback" with "He") as "Hs".
      rewrite list_insert_id //.
      wp_if_destruct.
      + rewrite decide_True; last word.
        wp_auto. wp_for_post.
        iDestruct (own_slice_split_all lim with "Hs") as "[Hs1 Hs2]"; first word.
        iApply ("HΦ" $! (slice.slice s raftpb.Entry.t (W64 0) lim)
                        (Z.to_nat (sint.Z lim))).
        iFrame "Hs1". iSplitR.
        { iPureIntro. split; [word | intros _; word]. }
        iIntros "Hs1".
        iDestruct (own_slice_combine lim s dq
                     (take (Z.to_nat (sint.Z lim)) es)
                     (drop (Z.to_nat (sint.Z lim)) es)
                     (W64 0) s.(slice.len) with "Hs1 Hs2") as "Hs";
          first (split; [rewrite length_take; word | word]).
        rewrite take_drop.
        iApply (own_slice_trivial_slice_2 with "Hs").
      + wp_for_post. iFrame. iPureIntro. word.
    - iApply ("HΦ" $! s (length es)). rewrite take_ge; last lia.
      iFrame. iSplit.
      + iPureIntro. split; [lia | intros _; lia].
      + iIntros "H". iFrame.
  Qed.

End LimitSizeProof.
