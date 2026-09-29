Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__slice.

Module RaftLogSliceProof (P : RAFTLOG__SLICE_POSTULATES) : RAFTLOG__SLICE.
Import P.

  (* Re-seal the log at the state it was opened at, from the pieces
     [iNamed "Hlog"] and [iNamed "Hcore"] named. *)
  Local Ltac reseal_log :=
    iApply own_raftLog_unfold; iExists _; iFrame "Hl";
    rewrite /own_raftLog_core;
    try (match goal with H : _ = interface.ok _ |- _ => rewrite H end);
    iFrame "∗#%";
    try (iPureIntro; done).

  (** The body has three shapes of exit, and the range premise kills every
      error path on the way:

      - [lo >= unstable.offset]: the result is [limitSize(u.slice(lo, hi))],
        re-sliced as [ents[0:len:len]].  [u.slice] hands out a read-only
        sub-slice, [limitSize] a prefix of that, and the three-index
        re-slice is the same pointer and length again -- so the read-only
        points-to travels through [own_slice_same_ptr_len]
        ([inv_raftlog.v]).
      - [lo < unstable.offset] and [cut = min(hi, offset)]: [Storage.Entries]
        hands out the stable part, read-only.  [cut] needs a case split,
        because Goose renders [min] as a [FuncUnfold] and the two arms are
        different ranges ([go.min] has no [PureWp]; [change ... with
        (replicate 2 go.uint64)] first, or the [FuncUnfold] instance will
        not match).  Four of the exits return exactly that slice.
      - the fifth exit is [extend(ents, unstable)]: a freshly allocated
        concatenation, made read-only before it is returned.

      Nothing is lent, so every exit re-seals the log as it found it
      ([reseal_log]).  (Until 2026-09-29 each exit built a loan instead,
      [own_raftLog_lend_page], with a wand chaining the lenders back.)

      Dead paths: [mustCheckOutOfBounds] returns [nil] (its own spec),
      [lo = hi] is excluded by [lo < hi], and [err = ErrCompacted] /
      [err = ErrUnavailable] are excluded because [Storage.Entries] returns
      [interface.nil] and [is_initialized] ([base.v], reached with
      [is_pkg_init_access]) says both globals are non-nil.  That is what
      makes the [Panicf] and the bare [panic] unreachable.

      *** Unfinished: one arithmetic side condition ([Hfitsx])

      [extend] computes [need := len(dst) + len(vals)] as a Go [int] and
      then [make([]Entry, need, need)], so [wp_extend] asks for
      [|ents| + |unstable| < 2^63].  Everything else about the call is
      discharged; that bound is **not derivable from the predicates as they
      stand**, and the missing step is the only [admit] in this file.

      What is available:
        - [|ents| = cut - lo <= |sents|], and [is_Storage]'s [Hbounded]
          gives [prev.index + |sents| < 2^61];
        - [|unstable| <= hi - offset <= |uents|], and [uents] is a Go slice,
          so [own_slice_len] gives [|uents| < 2^63].
      Their sum is [< 2^61 + 2^63], which clears [2^64] but not [2^63] --
      exactly the arithmetic [inv_raftlog.v]'s [Hnowrap] comment describes.
      Tightening [Hnowrap] to [2^63] does supply it, and was tried on
      2026-09-20 and reverted, because it makes [wp_raft__appendEntry]
      unprovable (a bound below [2^63] has to be *carried* across an
      [append], and no constant bound survives [+1]).

      So the triple as stated is **false** at a log with [~2^63] unstable
      entries: [need] wraps negative, [need <= cap(dst)] becomes true, and
      the code takes the [append] branch this development has not specified.
      It is the same shape as [campaign]'s term wrap
      (notes/false-statements.md), whose fix was a premise.  Here a premise
      has nowhere to live: [hasUnappliedConfChanges] opens [own_raftLog],
      whose entry lists are existential, so nothing at [hup] or [Step] can
      speak about [hi - lo]; and a bound *carried* in [own_raftLog] cannot
      be re-established by [appendEntry] (notes/decisions.md, 2026-09-20).
      What is being assumed is that the log fits in memory -- fewer than
      [2^63 - 2^61] unstable entries -- which the model, having no bound on
      memory, cannot know.  It is therefore the one deliberate, marked
      admission on the election path (the [(* Trusted *)] convention of
      [readonly.v]; [etc/tcb-report.py] counts it separately), recorded in
      notes/STATUS.md "Trust base" and notes/false-statements.md.  Everything
      up to [Hfitsx] is machine-checked. *)
  Lemma wp_raftLog__slice : wp_raftLog__slice_body.
  Proof.
    intros_ambient.
    intros l ls lo hi maxSize Hrange.
    destruct ls as [prev sents uents lcm lap]; logstate_simpl.
    destruct Hrange as (Hr1 & Hr2 & Hr3).
    assert (Hmc : (uint.Z prev.(raft.entryID.index') + 1 ≤ uint.Z lo ≤ uint.Z hi ≤
                   uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
                   + Z.of_nat (length uents) + 1)%Z) by lia.
    wp_start as "H". iNamed "H".
    iDestruct (is_pkg_init_access with "[$]") as "@".
    (* [err == ErrCompacted] and [err == ErrUnavailable] reduce to a [match]
       on the global's value, not to a [bool_decide], so the two globals have
       to be case-split; [is_initialized] says neither is [interface.nil]. *)
    destruct errCompacted; try (exfalso; by apply HErrCompacted).
    destruct errUnavailable; try (exfalso; by apply HErrUnavailable).
    wp_auto.
    wp_apply (wp_raftLog__mustCheckOutOfBounds l (logstate.mk prev sents uents lcm lap) lo hi Hmc
                with "[$Hlog]")
      as "Hlog". logstate_simpl.
    rewrite bool_decide_eq_false_2; last (intros ->; lia).
    wp_auto.
    iNamed "Hlog".
    iEval (rewrite /own_raftLog_core /=) in "Hcore". iNamed "Hcore".
    iDestruct (own_slice_len with "Huents") as %[Hulen Hulen'].
    wp_auto.
    wp_if_destruct.
    - (* the result lies entirely in the unstable suffix *)
      split_unstable l lv.
      assert (Hus : (uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset')
                     ≤ uint.Z lo ∧ uint.Z lo < uint.Z hi ∧
                     uint.Z hi ≤ uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset')
                                 + Z.of_nat (length uents))%Z) by lia.
      assert (Hnwu : (uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset')
                      + Z.of_nat (length uents) < 2^64)%Z) by lia.
      wp_apply (wp_unstable__slice _ _ _ _ _ Hus Hnwu with "[Huf Huents Huents_cap]")
        as "%s0 %es0 ((Huf & Huents_cap & Huents) & #Hs0 & (%Hlen0 & %Hin0 & %Hcap0))".
      { rewrite /own_unstable. iFrame. }
      wp_apply (wp_limitSize with "[$Hs0]")
        as "%s1 %nlim ([%Hn1a %Hn1b] & #Hs1 & _)".
      iDestruct (own_slice_len with "Hs1") as %[Hs1len Hs1len'].
      iDestruct (own_slice_wf with "Hs1") as %Hs1wf.
      assert (Hlen0' : (0 < length es0)%nat) by lia.
      assert (Hne0 : es0 ≠ []) by (destruct es0; simpl in *; [lia | done]).
      specialize (Hn1b Hne0).
      assert (Hnetake : take nlim es0 ≠ []).
      { intros Hc. assert (length (take nlim es0) = 0)%nat as Hz by (rewrite Hc //).
        rewrite length_take in Hz. lia. }
      rewrite decide_True; last word.
      wp_auto.
      iDestruct (own_slice_same_ptr_len s1
                   (slice.full_slice s1 raftpb.Entry.t (W64 0)
                      s1.(slice.len) s1.(slice.len)) with "Hs1") as "Hs2".
      { exact Hnetake. }
      { rewrite /= /slice_index_ref /= go.array_index_ref_0 //. }
      { simpl. word. }
      { simpl. word. }
      iDestruct ("Hlback" with "Huf") as "Hl".
      iApply ("HΦ" $! _ (take nlim es0)).
      iFrame "Hs2". iSplitL; last first.
      { iPureIntro. split_and!.
        - exact Hnetake.
        - rewrite length_take. lia.
        - intros e He. apply elem_of_app. right. apply Hin0.
          rewrite -(take_drop nlim es0). apply elem_of_app. by left. }
      reseal_log.
    - (* the result starts in the stable prefix: [lo < unstable.offset] *)
      iAssert (is_Storage lv.(raft.raftLog.storage')) as "#Hsto".
      { iExact "HisStorage". }
      iDestruct "Hsto" as (isv) "Hsto1". iNamed "Hsto1".
      iDestruct ("Hbounded" with "HStorage") as "[%Hsb HStorage]".
      change ([go.uint64; go.uint64]) with (replicate 2 go.uint64).
      rewrite func_unfold /minⁱᵐᵖˡ.
      wp_auto.
      destruct (decide (uint.Z hi <
                        uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset'))%Z)
        as [Hcut|Hcut].
      + (* cut = hi: the whole range is in storage *)
        rewrite bool_decide_eq_true_2; last done.
        wp_auto. rewrite Hstok /=.
        wp_apply ("HEntries" $! prev sents lo hi maxSize with "[$HStorage]").
        { iPureIntro. lia. }
        iIntros "%se %ese (#Hse & (%Hnee & %Hlene & %Hine & %Hcape) & HStorage)".
        wp_auto.
        rewrite bool_decide_eq_true_2; last word.
        wp_auto.
        iApply ("HΦ" $! se ese). iFrame "Hse". iSplitL; last first.
        { iPureIntro. split_and!.
          - exact Hnee.
          - lia.
          - intros ee Hee. apply elem_of_app. left. by apply Hine. }
        reseal_log.
      + (* cut = unstable.offset *)
        rewrite bool_decide_eq_false_2; last done.
        wp_auto. rewrite Hstok /=.
        wp_apply ("HEntries" $! prev sents lo
                    lv.(raft.raftLog.unstable').(raft.unstable.offset')
                    maxSize with "[$HStorage]").
        { iPureIntro. lia. }
        iIntros "%se %ese (#Hse & (%Hnee & %Hlene & %Hine & %Hcape) & HStorage)".
        iDestruct (own_slice_len with "Hse") as %[Hselen Hselen'].
        wp_auto.
        wp_if_destruct.
        { (* hi <= offset, i.e. hi = offset: the result is exactly the stable part *)
          iApply ("HΦ" $! se ese). iFrame "Hse". iSplitL; last first.
          { iPureIntro. split_and!.
            - exact Hnee.
            - lia.
            - intros ee Hee. apply elem_of_app. left. by apply Hine. }
          reseal_log. }
        wp_if_destruct.
        { (* storage returned fewer entries than asked for: stop there *)
          iApply ("HΦ" $! se ese). iFrame "Hse". iSplitL; last first.
          { iPureIntro. split_and!.
            - exact Hnee.
            - lia.
            - intros ee Hee. apply elem_of_app. left. by apply Hine. }
          reseal_log. }
        wp_apply (wp_entsSize with "[$Hse]") as "%sz1 _".
        wp_if_destruct.
        { (* the stable part already reaches [maxSize] *)
          iApply ("HΦ" $! se ese). iFrame "Hse". iSplitL; last first.
          { iPureIntro. split_and!.
            - exact Hnee.
            - lia.
            - intros ee Hee. apply elem_of_app. left. by apply Hine. }
          reseal_log. }
        split_unstable l lv.
        assert (Hus : (uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset')
                       ≤ uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset') ∧
                       uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset')
                       < uint.Z hi ∧
                       uint.Z hi ≤ uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset')
                                   + Z.of_nat (length uents))%Z) by lia.
        assert (Hnwu : (uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset')
                        + Z.of_nat (length uents) < 2^64)%Z) by lia.
        wp_apply (wp_unstable__slice _ _ _ _ _ Hus Hnwu with "[Huf Huents Huents_cap]")
          as "%s0 %es0 ((Huf & Huents_cap & Huents) & #Hs0 & (%Hlen0 & %Hin0 & %Hcap0))".
        { rewrite /own_unstable. iFrame. }
        wp_apply (wp_limitSize with "[$Hs0]")
          as "%s1 %nlim ([%Hn1a %Hn1b] & #Hs1 & _)".
        iDestruct ("Hlback" with "Huf") as "Hl".
        assert (Hlen0' : (0 < length es0)%nat) by lia.
        assert (Hne0 : es0 ≠ []) by (destruct es0; simpl in *; [lia | done]).
        specialize (Hn1b Hne0).
        assert (Hlentake : length (take nlim es0) = nlim) by (rewrite length_take; lia).
        assert (Hintake : ∀ ee, ee ∈ take nlim es0 → ee ∈ uents).
        { intros ee Hee. apply Hin0. rewrite -(take_drop nlim es0).
          apply elem_of_app. by left. }
        assert (Hcapx : (sint.Z se.(slice.cap) < Z.of_nat (length ese)
                         + Z.of_nat (length (take nlim es0)))%Z)
          by (rewrite Hcape; word).
        assert (Hfitsx : (Z.of_nat (length ese)
                          + Z.of_nat (length (take nlim es0)) < 2^63)%Z).
        { (* NOT PROVABLE from the current predicates -- see the header
             comment.  [Hsb] gives [prev.index + |sents| < 2^61] and
             [Hulen] gives [|uents| < 2^63]; the sum of the two parts is
             bounded only by [2^61 + 2^63]. *)
          admit. }
        wp_if_destruct.
        * (* [len(unstable) == 1]: one more size check before giving up *)
          wp_apply (wp_entsSize with "[$Hs1]") as "%sz2 _".
          wp_if_destruct.
          -- (* the single unstable entry does not fit *)
             iApply ("HΦ" $! se ese). iFrame "Hse". iSplitL; last first.
             { iPureIntro. split_and!.
               - exact Hnee.
               - lia.
               - intros ee Hee. apply elem_of_app. left. by apply Hine. }
             reseal_log.
          -- iApply wp_fupd.
             wp_apply (wp_extend _ _ _ _ _ _ Hcapx Hfitsx with "[$Hse $Hs1]")
               as "%sx (Hsx & _ & _ & _)".
             iMod (own_slice_persist with "Hsx") as "#Hsx".
             iModIntro.
             iApply ("HΦ" $! sx (ese ++ take nlim es0)).
             iFrame "Hsx". iSplitL; last first.
             { iPureIntro. split_and!.
               - intros Hc. destruct ese as [|a ese']; [by apply Hnee | discriminate Hc].
               - rewrite length_app. lia.
               - intros ee Hee. apply elem_of_app in Hee as [Hee|Hee].
                 + apply elem_of_app. left. by apply Hine.
                 + apply elem_of_app. right. by apply Hintake. }
             reseal_log.
        * iApply wp_fupd.
          wp_apply (wp_extend _ _ _ _ _ _ Hcapx Hfitsx with "[$Hse $Hs1]")
            as "%sx (Hsx & _ & _ & _)".
          iMod (own_slice_persist with "Hsx") as "#Hsx".
          iModIntro.
          iApply ("HΦ" $! sx (ese ++ take nlim es0)).
          iFrame "Hsx". iSplitL; last first.
          { iPureIntro. split_and!.
            - intros Hc. destruct ese as [|a ese']; [by apply Hnee | discriminate Hc].
            - rewrite length_app. lia.
            - intros ee Hee. apply elem_of_app in Hee as [Hee|Hee].
              + apply elem_of_app. left. by apply Hine.
              + apply elem_of_app. right. by apply Hintake. }
          reseal_log.
  (* The only [admit] above is [Hfitsx]: "the log fits in memory".  See the
     header comment; deliberate. *)
  Admitted. (* Trusted *)

End RaftLogSliceProof.
