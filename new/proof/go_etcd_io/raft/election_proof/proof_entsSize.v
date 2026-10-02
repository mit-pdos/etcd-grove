Require Export New.proof.go_etcd_io.raft.election_proof.postulates_entsSize.

Module EntsSizeProof (P : ENTSSIZE_POSTULATES) : ENTSSIZE.
Import P.

  (** A [slice.for_range] accumulating [Entry.Size()] into [size].  Since the
      spec says nothing about the value, the loop invariant carries no
      arithmetic at all -- only the three mutable locations and the index
      bound that the [IndexRef] needs.  [ent] is allocated *outside* the
      loop and written on every iteration, so it is existentially quantified
      inside the invariant (the [cur] lesson from [proof_raft__campaign.v]).

      [Entry.Size] has a pointer receiver and the range variable [ent] is
      that pointer, so [wp_Entry__Size] applies to [ent_ptr] directly. *)
  Lemma wp_entsSize : wp_entsSize_body.
  Proof.
    intros_ambient.
    intros s es dq.
    wp_start as "H". iNamed "H". wp_auto.
    iDestruct (own_slice_len with "Hs") as %[Hlen Hlen'].
    iAssert (∃ (n sz : w64) (ev : raftpb.Entry.t),
      "i" ∷ i_ptr ↦ n ∗
      "size" ∷ size_ptr ↦ sz ∗
      "ent" ∷ ent_ptr ↦ ev ∗
      "%Hn" ∷ ⌜ (0 ≤ sint.Z n ≤ Z.of_nat (length es))%Z ⌝)%I
      with "[i size ent]" as "IH".
    { iFrame. iPureIntro. word. }
    wp_for "IH".
    wp_if_destruct.
    - assert (∃ e, es !! Z.to_nat (sint.Z n) = Some e) as [e He].
      { apply lookup_lt_is_Some_2. word. }
      case_decide as Hdec; [clear Hdec | exfalso; apply Hdec; word].
      wp_apply (wp_load_slice_index (V:=raftpb.Entry.t) (t:=raftpb.Entry)
                  s (sint.Z n) es dq e with "[$Hs]") as "Hs";
        try first [ word | iPureIntro; exact He | tc_solve | done ].
      wp_apply (wp_Entry__Size with "[$ent]") as "%sz2 ent".
      wp_for_post.
      iFrame. iPureIntro. word.
    - iApply "HΦ". iFrame.
  Qed.

End EntsSizeProof.
