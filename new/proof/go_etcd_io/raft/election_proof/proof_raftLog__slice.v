Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__slice.

Module RaftLogSliceProof (P : RAFTLOG__SLICE_POSTULATES) : RAFTLOG__SLICE.
Import P.

  (** The body has three shapes of exit, and the range premise kills every
      error path on the way:

      - [lo >= unstable.offset]: the page is [limitSize(u.slice(lo, hi))],
        re-sliced as [ents[0:len:len]].  [u.slice] hands its result out
        lent, [limitSize] lends a prefix of that, and the three-index
        re-slice is the same pointer and length again -- so the page's
        points-to travels through [own_slice_same_ptr_len] ([inv_raftlog.v])
        and the wand chains the two lenders back together.
      - [lo < unstable.offset] and [cut = min(hi, offset)]: [Storage.Entries]
        lends the stable part.  [cut] needs a case split, because Goose
        renders [min] as a [FuncUnfold] and the two arms are different pages
        ([go.min] has no [PureWp]; [change ... with (replicate 2 go.uint64)]
        first, or the [FuncUnfold] instance will not match).  Four of the
        exits return exactly that lent page.
      - the fifth exit is [extend(ents, unstable)]: a freshly allocated
        concatenation, so the wand drops it and puts the two lenders back.

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
    intros l ls lo hi maxSize Hpg Hrange.
    destruct ls as [prev sents uents lcm lap lpg]; logstate_simpl; subst lpg.
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
    wp_apply (wp_raftLog__mustCheckOutOfBounds l (logstate.mk prev sents uents lcm lap None) lo hi eq_refl Hmc
                with "[$Hlog]")
      as "Hlog". logstate_simpl.
    rewrite bool_decide_eq_false_2; last (intros ->; lia).
    wp_auto.
    iNamed "Hlog".
    iEval (rewrite /own_raftLog_core /=) in "Hcore". iNamed "Hcore".
    iDestruct (own_slice_len with "Huents") as %[Hulen Hulen'].
    wp_auto.
    wp_if_destruct.
    - (* the page lies entirely in the unstable suffix *)
      split_unstable l lv.
      assert (Hus : (uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset')
                     ≤ uint.Z lo ∧ uint.Z lo < uint.Z hi ∧
                     uint.Z hi ≤ uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset')
                                 + Z.of_nat (length uents))%Z) by lia.
      assert (Hnwu : (uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset')
                      + Z.of_nat (length uents) < 2^64)%Z) by lia.
      wp_apply (wp_unstable__slice _ _ _ _ _ Hus Hnwu with "[Huf Huents Huents_cap]")
        as "%s0 %es0 ((Huf & Huents_cap & Hback0) & Hs0 & (%Hlen0 & %Hin0 & %Hcap0))".
      { rewrite /own_unstable. iFrame. }
      wp_apply (wp_limitSize with "[$Hs0]")
        as "%s1 %nlim ([%Hn1a %Hn1b] & Hs1 & Hback1)".
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
      iApply ("HΦ" $! _ (take nlim es0) (DfracOwn 1)).
      iFrame "Hs2". iSplitL; last first.
      { iPureIntro. split_and!.
        - exact Hnetake.
        - rewrite length_take. lia.
        - intros e He. apply elem_of_app. right. apply Hin0.
          rewrite -(take_drop nlim es0). apply elem_of_app. by left. }
      iApply (own_raftLog_lend_page with "Hl [//] [//]"). iIntros "Hs2".
      iDestruct (own_slice_same_ptr_len
                   (slice.full_slice s1 raftpb.Entry.t (W64 0)
                      s1.(slice.len) s1.(slice.len)) s1 with "Hs2") as "Hs1".
      { exact Hnetake. }
      { rewrite /= /slice_index_ref /= go.array_index_ref_0 //. }
      { simpl. word. }
      { word. }
      iDestruct ("Hback1" with "Hs1") as "Hs0".
      iDestruct ("Hback0" with "Hs0") as "Huents".
      rewrite /own_raftLog_core. iFrame "∗#%".
    - (* the page starts in the stable prefix: [lo < unstable.offset] *)
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
      + (* cut = hi: the whole page is in storage *)
        rewrite bool_decide_eq_true_2; last done.
        wp_auto. rewrite Hstok /=.
        wp_apply ("HEntries" $! prev sents lo hi maxSize with "[$HStorage]").
        { iPureIntro. lia. }
        iIntros "%se %ese %dqe (Hse & (%Hnee & %Hlene & %Hine & %Hcape) & Hbacke)".
        wp_auto.
        rewrite bool_decide_eq_true_2; last word.
        wp_auto.
        iApply ("HΦ" $! se ese dqe). iFrame "Hse". iSplitL; last first.
        { iPureIntro. split_and!.
          - exact Hnee.
          - lia.
          - intros ee Hee. apply elem_of_app. left. by apply Hine. }
        iApply (own_raftLog_lend_page with "Hl [//] [//]").
          iIntros "Hse". iDestruct ("Hbacke" with "Hse") as "HStorage".
        rewrite /own_raftLog_core Hstok. iFrame "∗#%". all: (iPureIntro; done).
      + (* cut = unstable.offset *)
        rewrite bool_decide_eq_false_2; last done.
        wp_auto. rewrite Hstok /=.
        wp_apply ("HEntries" $! prev sents lo
                    lv.(raft.raftLog.unstable').(raft.unstable.offset')
                    maxSize with "[$HStorage]").
        { iPureIntro. lia. }
        iIntros "%se %ese %dqe (Hse & (%Hnee & %Hlene & %Hine & %Hcape) & Hbacke)".
        iDestruct (own_slice_len with "Hse") as %[Hselen Hselen'].
        wp_auto.
        wp_if_destruct.
        { (* hi <= offset, i.e. hi = offset: the page is exactly the stable part *)
          iApply ("HΦ" $! se ese dqe). iFrame "Hse". iSplitL; last first.
          { iPureIntro. split_and!.
            - exact Hnee.
            - lia.
            - intros ee Hee. apply elem_of_app. left. by apply Hine. }
          iApply (own_raftLog_lend_page with "Hl [//] [//]").
          iIntros "Hse". iDestruct ("Hbacke" with "Hse") as "HStorage".
          rewrite /own_raftLog_core Hstok. iFrame "∗#%". all: (iPureIntro; done). }
        wp_if_destruct.
        { (* storage returned a short page: stop there *)
          iApply ("HΦ" $! se ese dqe). iFrame "Hse". iSplitL; last first.
          { iPureIntro. split_and!.
            - exact Hnee.
            - lia.
            - intros ee Hee. apply elem_of_app. left. by apply Hine. }
          iApply (own_raftLog_lend_page with "Hl [//] [//]").
          iIntros "Hse". iDestruct ("Hbacke" with "Hse") as "HStorage".
          rewrite /own_raftLog_core Hstok. iFrame "∗#%". all: (iPureIntro; done). }
        wp_apply (wp_entsSize with "[$Hse]") as "%sz1 Hse".
        wp_if_destruct.
        { (* the stable part already fills the page *)
          iApply ("HΦ" $! se ese dqe). iFrame "Hse". iSplitL; last first.
          { iPureIntro. split_and!.
            - exact Hnee.
            - lia.
            - intros ee Hee. apply elem_of_app. left. by apply Hine. }
          iApply (own_raftLog_lend_page with "Hl [//] [//]").
          iIntros "Hse". iDestruct ("Hbacke" with "Hse") as "HStorage".
          rewrite /own_raftLog_core Hstok. iFrame "∗#%". all: (iPureIntro; done). }
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
          as "%s0 %es0 ((Huf & Huents_cap & Hback0) & Hs0 & (%Hlen0 & %Hin0 & %Hcap0))".
      { rewrite /own_unstable. iFrame. }
        wp_apply (wp_limitSize with "[$Hs0]")
          as "%s1 %nlim ([%Hn1a %Hn1b] & Hs1 & Hback1)".
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
             [Hulen] gives [|uents| < 2^63]; the sum of the two pages is
             bounded only by [2^61 + 2^63]. *)
          admit. }
        wp_if_destruct.
        * (* [len(unstable) == 1]: one more size check before giving up *)
          wp_apply (wp_entsSize with "[$Hs1]") as "%sz2 Hs1".
          wp_if_destruct.
          -- (* the single unstable entry does not fit *)
             iDestruct ("Hback1" with "Hs1") as "Hs0".
             iDestruct ("Hback0" with "Hs0") as "Huents".
             iDestruct ("Hlback" with "Huf") as "Hl".
             iApply ("HΦ" $! se ese dqe). iFrame "Hse". iSplitL; last first.
             { iPureIntro. split_and!.
               - exact Hnee.
               - lia.
               - intros ee Hee. apply elem_of_app. left. by apply Hine. }
             iApply (own_raftLog_lend_page with "Hl [//] [//]").
          iIntros "Hse". iDestruct ("Hbacke" with "Hse") as "HStorage".
             rewrite /own_raftLog_core Hstok. iFrame "∗#%". all: (iPureIntro; done).
          -- wp_apply (wp_extend _ _ _ _ _ _ Hcapx Hfitsx with "[$Hse $Hs1]")
               as "%sx (Hsx & Hsx_cap & Hse & Hs1)".
             iDestruct ("Hlback" with "Huf") as "Hl".
             iApply ("HΦ" $! sx (ese ++ take nlim es0) (DfracOwn 1)).
             iFrame "Hsx". iSplitL; last first.
             { iPureIntro. split_and!.
               - intros Hc. destruct ese as [|a ese']; [by apply Hnee | discriminate Hc].
               - rewrite length_app. lia.
               - intros ee Hee. apply elem_of_app in Hee as [Hee|Hee].
                 + apply elem_of_app. left. by apply Hine.
                 + apply elem_of_app. right. by apply Hintake. }
             iApply (own_raftLog_lend_page with "Hl [//] [//]"). iIntros "Hsx".
             iDestruct ("Hback1" with "Hs1") as "Hs0".
             iDestruct ("Hback0" with "Hs0") as "Huents".
             iDestruct ("Hbacke" with "Hse") as "HStorage".
             rewrite /own_raftLog_core Hstok. iFrame "∗#%". all: (iPureIntro; done).
        * wp_apply (wp_extend _ _ _ _ _ _ Hcapx Hfitsx with "[$Hse $Hs1]")
            as "%sx (Hsx & Hsx_cap & Hse & Hs1)".
          iDestruct ("Hlback" with "Huf") as "Hl".
          iApply ("HΦ" $! sx (ese ++ take nlim es0) (DfracOwn 1)).
          iFrame "Hsx". iSplitL; last first.
          { iPureIntro. split_and!.
            - intros Hc. destruct ese as [|a ese']; [by apply Hnee | discriminate Hc].
            - rewrite length_app. lia.
            - intros ee Hee. apply elem_of_app in Hee as [Hee|Hee].
              + apply elem_of_app. left. by apply Hine.
              + apply elem_of_app. right. by apply Hintake. }
          iApply (own_raftLog_lend_page with "Hl [//] [//]"). iIntros "Hsx".
          iDestruct ("Hback1" with "Hs1") as "Hs0".
          iDestruct ("Hback0" with "Hs0") as "Huents".
          iDestruct ("Hbacke" with "Hse") as "HStorage".
          rewrite /own_raftLog_core Hstok. iFrame "∗#%". all: (iPureIntro; done).
  (* The only [admit] above is [Hfitsx]: "the log fits in memory".  See the
     header comment; deliberate. *)
  Admitted. (* Trusted *)

End RaftLogSliceProof.
