Require Export New.proof.go_etcd_io.raft.election_proof.postulates_Inflights__FreeLE.

Module InflightsFreeLEProof (P : INFLIGHTS__FREELE_POSTULATES) : INFLIGHTS__FREELE.

  (** The tail after the loop, shared by its two exits ([break] and
      [i = count]): [count -= i; bytes -= bytes; start = idx;
      if count == 0 { start = 0 }], then re-establish [inflights_ok] from
      the loop invariant [Hidx] and the ring invariant [Hring]. *)
  Local Ltac freele_finish Hidx Hring iv iw :=
    try wp_auto;
    (* the new [count] as an integer, once, so that the many pure goals
       below are [lia]'s rather than [word]'s (halves the check time) *)
    let Hc := fresh "Hc'" in
    assert (sint.Z (word.sub iv.(tracker.Inflights.count') iw)
            = sint.Z iv.(tracker.Inflights.count') - sint.Z iw) as Hc by word;
    let H0 := fresh "H0" in
    assert (sint.Z (W64 0) = 0) as H0 by reflexivity;
    wp_if_destruct;
    iApply "HΦ"; rewrite /own_inflights; iFrame "Hiv"; iFrame; iPureIntro;
    rewrite /inflights_ok /= ?Hc ?H0;
    destruct Hidx as [[? ?]|[? ?]]; destruct Hring;
    split_and!; solve [ done | lia | left; lia | right; lia | word ].

  (** The loop invariant: [0 ≤ i ≤ count] and [idx = (start + i) mod size],
      written as its two cases so that [word]/[lia] can use it.  An
      occupied slot [idx] (i.e. [i < count]) is inside the buffer by
      [inflights_ok]'s last conjunct: either the occupied range does not
      wrap and ends inside the buffer, or the buffer is the whole ring. *)
  Lemma wp_Inflights__FreeLE : wp_Inflights__FreeLE_body.
  Proof.
    intros_ambient.
    intros l iv buf to.
    wp_start as "H". iNamed "H". iNamed "Hin".
    iDestruct (own_slice_len with "Hbuf") as %[Hblen Hblen0].
    destruct Hinfl_ok as (Hs0 & Hc & Hbl & Hsz & Hstart & Hring).
    wp_auto.
    destruct (decide (iv.(tracker.Inflights.count') = W64 0)) as [Hc0|Hc0].
    { (* exit 1, empty window *)
      rewrite bool_decide_eq_true_2; last done.
      wp_auto. iApply "HΦ". iFrame. iPureIntro. split; first done.
      split_and!; done. }
    rewrite bool_decide_eq_false_2; last done.
    (* a non-empty window: [0 < count ≤ size], so [start < size], and the
       occupied slot [start] is inside the buffer *)
    assert (0 < sint.Z iv.(tracker.Inflights.count')) as Hcpos.
    { assert (sint.Z iv.(tracker.Inflights.count') ≠ 0); last lia.
      intros Hz. apply Hc0. word. }
    assert (sint.Z iv.(tracker.Inflights.start') < sint.Z iv.(tracker.Inflights.size'))
      as Hslt by (destruct Hstart; lia).
    assert (sint.Z iv.(tracker.Inflights.start') < Z.of_nat (length buf)) as Hsbuf
      by (destruct Hring; lia).
    assert (∃ e0, buf !! Z.to_nat (sint.Z iv.(tracker.Inflights.start')) = Some e0)
      as [e0 He0] by (apply lookup_lt_is_Some_2; lia).
    wp_auto.
    rewrite decide_True; last word.
    iDestruct (own_slice_elem_acc (sint.Z iv.(tracker.Inflights.start')) e0 with "Hbuf")
      as "[He Hback]"; [lia|done|].
    wp_auto.
    iDestruct ("Hback" with "He") as "Hbuf". rewrite list_insert_id //.
    wp_if_destruct.
    { (* exit 1, [to] is left of the window *)
      iApply "HΦ". iFrame. iPureIntro. split; first done.
      split_and!; done. }
    (* the loop: [i] counts freed slots, [idx] is [start + i] mod [size] *)
    iAssert (∃ (idxv iw bv : w64),
      "idx" ∷ idx_ptr ↦ idxv ∗ "i" ∷ i_ptr ↦ iw ∗ "bytes" ∷ bytes_ptr ↦ bv ∗
      "%Hi" ∷ ⌜ 0 ≤ sint.Z iw ≤ sint.Z iv.(tracker.Inflights.count')%Z ⌝ ∗
      "%Hidx" ∷ ⌜ ((sint.Z iv.(tracker.Inflights.start') + sint.Z iw
                     < sint.Z iv.(tracker.Inflights.size') ∧
                   sint.Z idxv = sint.Z iv.(tracker.Inflights.start') + sint.Z iw) ∨
                  (sint.Z iv.(tracker.Inflights.size')
                     ≤ sint.Z iv.(tracker.Inflights.start') + sint.Z iw ∧
                   sint.Z idxv = sint.Z iv.(tracker.Inflights.start') + sint.Z iw
                                 - sint.Z iv.(tracker.Inflights.size')))%Z ⌝)%I
      with "[idx i bytes]" as "IH".
    { iExists iv.(tracker.Inflights.start'), (W64 0), (W64 0). iFrame. iPureIntro. split; first word. left. split; word. }
    wp_for "IH".
    wp_if_destruct.
    - (* [i < count]: slot [idx] is occupied, hence inside the buffer *)
      assert (0 ≤ sint.Z idxv < Z.of_nat (length buf)) as Hidxb
        by (destruct Hidx; destruct Hring; lia).
      assert (∃ e, buf !! Z.to_nat (sint.Z idxv) = Some e) as [e He]
        by (apply lookup_lt_is_Some_2; lia).
      rewrite decide_True; last word.
      iDestruct (own_slice_elem_acc (sint.Z idxv) e with "Hbuf")
        as "[He Hback]"; [lia|done|].
      wp_auto.
      iDestruct ("Hback" with "He") as "Hbuf". rewrite list_insert_id //.
      wp_if_destruct.
      + (* [break]: the first inflight past [to] *)
        wp_for_post.
        freele_finish Hidx Hring iv iw.
      + try wp_auto.
        rewrite decide_True; last word.
        iDestruct (own_slice_elem_acc (sint.Z idxv) e with "Hbuf")
          as "[He Hback]"; [lia|done|].
        wp_auto.
        iDestruct ("Hback" with "He") as "Hbuf". rewrite list_insert_id //.
        try wp_auto.
        wp_if_destruct.
        * (* [idx] wraps *)
          wp_for_post. iFrame. iPureIntro. split; first word.
          right. split; word.
        * wp_for_post. iFrame. iPureIntro. split; first word.
          destruct Hidx as [[? ?]|[? ?]]; [left|right]; split; word.
    - (* [i = count]: every inflight is freed *)
      freele_finish Hidx Hring iv iw.
  Qed.

End InflightsFreeLEProof.
