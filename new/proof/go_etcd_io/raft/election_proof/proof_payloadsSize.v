Require Export New.proof.go_etcd_io.raft.election_proof.postulates_payloadsSize.

Module PayloadsSizeProof (P : PAYLOADSSIZE_POSTULATES) : PAYLOADSSIZE.
Import P.

  (** [entsSize]'s loop.  The accumulator is existential, with one
      implication in the invariant: *if* every payload is empty it is still
      [0].  (It used to be pinned to [0] under a [Forall] premise on the
      lemma; widened 2026-09-20 for [maybeSendAppend], which weighs entries
      that came out of the log.)  [ent] is allocated outside the loop and
      written on every iteration, so it too is existentially quantified
      ([notes/gotchas.md], "A [for … range] loop variable must be inside the
      [wp_for] invariant"). *)
  Lemma wp_payloadsSize : wp_payloadsSize_body.
  Proof.
    intros_ambient.
    intros s es dq.
    wp_start as "H". iNamed "H". wp_auto.
    iDestruct (own_slice_len with "Hs") as %[Hlen Hlen'].
    iAssert (∃ (n acc : w64) (ev : raftpb.Entry.t),
      "i" ∷ i_ptr ↦ n ∗
      "size" ∷ s_ptr ↦ acc ∗
      "ent" ∷ e_ptr ↦ ev ∗
      "%Hn" ∷ ⌜ (0 ≤ sint.Z n ≤ Z.of_nat (length es))%Z ⌝ ∗
      "%Hacc" ∷ ⌜ Forall (λ e, sint.Z e.(raftpb.Entry.Data').(slice.len) = 0) es →
                  acc = W64 0 ⌝)%I
      with "[i s e]" as "IH".
    { iFrame. iPureIntro. split; [word|done]. }
    wp_for "IH".
    wp_if_destruct.
    - assert (∃ e, es !! Z.to_nat (sint.Z n) = Some e) as [e He].
      { apply lookup_lt_is_Some_2. word. }
      case_decide as Hdec; [clear Hdec | exfalso; apply Hdec; word].
      wp_apply (wp_load_slice_index (V:=raftpb.Entry.t) (t:=raftpb.Entry)
                  s (sint.Z n) es dq e with "[$Hs]") as "Hs";
        try first [ word | iPureIntro; exact He | tc_solve | done ].
      (* [payloadSize] has no premise and returns nothing, so [wp_apply] runs
         straight on through the accumulating store: the goal comes back at
         [wp_for_post] with [size] holding [0 + len(e.Data)]. *)
      wp_apply wp_payloadSize.
      wp_for_post.
      iFrame. iPureIntro. split; first word.
      (* if every payload is empty then so is this one, and the accumulator
         was [0] by the invariant *)
      intros Hzero.
      pose proof (Forall_lookup_1 _ _ _ _ Hzero He) as Hz0.
      rewrite (Hacc Hzero). word.
    - iApply "HΦ". iFrame. iPureIntro. exact Hacc.
  Qed.

End PayloadsSizeProof.
