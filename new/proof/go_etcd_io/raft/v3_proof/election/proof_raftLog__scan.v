Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raftLog__scan.

Module RaftLogScanProof (P : RAFTLOG__SCAN_POSTULATES) : RAFTLOG__SCAN.
Import P.

  (** [scan] is

        for lo < hi {
          ents, err := l.slice(lo, hi, pageSize)
          if err != nil { return err }
          if len(ents) == 0 { return fmt.Errorf("got 0 entries in [%d, %d)") }
          if err := v(ents); err != nil { return err }
          lo += uint64(len(ents))
        }
        return nil

      Note what [slice] is called with: the *whole* remaining range
      [[lo, hi)] with [pageSize] as its [maxSize], not [min(hi, lo+pageSize)]
      — the page is cut by byte budget inside [slice], and the only thing
      [scan] knows about it is what [wp_raftLog__slice_at] states.

      Three things carry the proof.

      - The loop invariant is just the moving [lo]: [prev.index + 1 <= lo <=
        hi], with [own_raftLog_at] and the caller's [I] alongside.  Only
        [lo] is written, so [hi], [pageSize], [l] and [v] stay in the frame
        [wp_for] sweeps up.  No termination measure is needed: [wp_for] is
        Löb induction under a partial-correctness [WP].
      - Both error returns are dead.  [slice]'s spec returns
        [#interface.nil] for the error, so the first [if] is skipped by
        [wp_auto] alone; the second needs [es ≠ []] from that spec, which
        via [slice_len_Z] gives [s.len ≠ 0].  The callback error is dead by
        construction: [scan_closure] demands [#interface.nil].
      - The callback gets the page with [Forall Pred es], which
        [Forall_sublist_of] derives from the premise [Forall Pred
        (sents ++ uents)] and the spec's "every entry of the page is an
        entry of the log".

      The bound [lo + len(ents) <= hi] — needed both to re-establish the
      invariant and to show the [w64] addition does not wrap — is exactly
      [slice]'s [length es <= hi - lo].  [own_raftLog_at]'s [Hnowrap] is not
      needed and the predicate stays sealed throughout. *)
  Lemma wp_raftLog__scan_at : wp_raftLog__scan_at_body.
  Proof.
    intros_ambient.
    intros l prev sents uents lo hi pageSize f I Pred Hrange HP.
    wp_start as "H". iNamed "H". wp_auto.
    iAssert (∃ (cur : w64),
       "lo" ∷ lo_ptr ↦ cur ∗
       "Hlog" ∷ own_raftLog_at l prev sents uents ∗
       "HI" ∷ I ∗
       "%Hcur" ∷ ⌜ (uint.Z prev.(raft.entryID.index') + 1 ≤ uint.Z cur ≤
                    uint.Z hi)%Z ⌝)%I
      with "[lo Hlog HI]" as "IH".
    { iFrame. iPureIntro. lia. }
    wp_for "IH".
    wp_if_destruct.
    - (* one more page: [cur < hi], so [slice]'s range premise holds *)
      assert ((uint.Z prev.(raft.entryID.index') + 1 ≤ uint.Z cur ∧
               uint.Z cur < uint.Z hi ∧
               uint.Z hi ≤ uint.Z prev.(raft.entryID.index')
                 + Z.of_nat (length sents) + Z.of_nat (length uents) + 1)%Z)
        as Hsl by lia.
      wp_apply (wp_raftLog__slice_at l prev sents uents cur hi pageSize Hsl
                 with "[$Hlog]")
        as "%s %es %dq (Hes & (%Hne & %Hlen & %Hin) & Hback)".
      (* the "got 0 entries" error is dead: the page is non-empty *)
      iDestruct (slice_len_Z with "Hes") as %Hslen.
      assert (length es ≠ 0)%nat as Hlen0 by (destruct es; [done | simpl; lia]).
      assert (s.(slice.len) ≠ W64 0) as Hsne.
      { intros Heq0. rewrite Heq0 in Hslen. word. }
      rewrite bool_decide_eq_false_2 //. wp_auto.
      (* every entry of the page is an entry of the log, so [Pred] holds *)
      iAssert (⌜ Forall Pred es ⌝)%I as "HPes".
      { iPureIntro. eapply Forall_sublist_of; [exact HP | exact Hin]. }
      wp_apply ("Hf" with "[$Hes $HPes $HI]") as "[Hes HI]".
      iDestruct ("Hback" with "Hes") as "Hlog".
      wp_for_post.
      iFrame. iPureIntro. word.
    - (* [cur = hi]: the range is exhausted and the function returns nil *)
      iApply "HΦ". iFrame.
  Qed.

End RaftLogScanProof.
