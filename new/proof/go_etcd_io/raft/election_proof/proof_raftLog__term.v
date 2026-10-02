Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__term.

Section helper.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.

(** What [Storage.Term] answers ([term_at prev stored i], [inv_storage.v])
    is [plog_term_at] of the whole log on the visible stable range: the
    stored entries agree with [sents] there, [sents] being a prefix. *)
Local Lemma term_at_visible (prev : raft.entryID.t) (sents uents stored : list raftpb.Entry.t)
    (i t : w64) :
  sents `prefix_of` stored →
  (uint.Z prev.(raft.entryID.index') ≤ uint.Z i
   ≤ uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents))%Z →
  term_at prev stored i = Some t →
  plog_term_at prev (sents ++ uents) i = Some t.
Proof.
  intros [k ->] Hr Ht. rewrite /term_at in Ht.
  rewrite /plog_term_at decide_False; [|lia].
  revert Ht.
  destruct (decide (uint.Z i = uint.Z prev.(raft.entryID.index'))) as [Heq|Heq].
  - simpl. done.
  - simpl. intros Ht.
    rewrite lookup_app_l in Ht; [|lia]. rewrite lookup_app_l; [done|lia].
Qed.

End helper.

Module RaftLogTermProof (P : RAFTLOG__TERM_POSTULATES) : RAFTLOG__TERM.
Import P.

  (** Four exits, in the order the body takes them
      ([raftLog__termⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:1063):

      - [unstable.maybeTerm] said yes -- the index is in the unstable
        suffix, the term comes back with a [nil] error, and [ok]'s iff puts
        [i] in range;
      - [i + 1 < l.firstIndex()] -- [(0, ErrCompacted)].  This is the one
        place [i + 1] can wrap: at [i = 2^64 - 1] the sum is [0], which is
        below [firstIndex = prev.index + 1 >= 1], so the branch is taken.
        That is consistent with the iff because [Hnowrap] puts every
        in-range [i] at [<= 2^64 - 2].  The error is non-[nil] by
        [is_initialized]'s [HErrCompacted];
      - [i > l.lastIndex()] -- [(0, ErrUnavailable)], likewise;
      - otherwise [Storage.Term(i)].  Falling through both tests gives
        [prev.index <= i <= prev.index + |sents| + |uents|], and
        [maybeTerm]'s [ok = false] rules out the unstable window, so
        [i <= prev.index + |sents|]: exactly [HTerm]'s premise.  [HTerm]
        returns a [nil] error, so the [panic] below it is unreachable.

      The two error returns read package-level globals, which is why
      [is_pkg_init_access] appears at the top -- same reason as in
      [proof_raftLog__slice.v], except that this body only *returns* them
      and never compares against them, so the interface values need not be
      case-split.  Their non-[nil]-ness is what gives the [->] half of the
      postcondition's iff on those two exits. *)

  Lemma wp_raftLog__term : wp_raftLog__term_body.
  Proof.
    intros_ambient.
    intros l ls i.
    destruct ls as [prev sents uents lcm lap]; logstate_simpl.
    wp_start as "H". iNamed "H".
    iDestruct (is_pkg_init_access with "[$]") as "@".
    iNamed "Hlog".
    iEval (rewrite /own_raftLog_core /=) in "Hcore". iNamed "Hcore". wp_auto.
    assert (Hnw : (uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset') +
                   Z.of_nat (length uents) < 2^64)%Z) by lia.
    iAssert (is_Storage lv.(raft.raftLog.storage')) as "#Hsto".
    { iExact "HisStorage". }
    iDestruct "Hsto" as (isv) "(%Hstok & #HLI & #HFI & #HT & #HE & #HB & #HSnap)".
    split_unstable l lv.
    wp_apply (wp_unstable__maybeTerm _ _ _ _ Hnosnap Hnw
                with "[Huf Huents Huents_cap]")
      as "%t %ok ((Huf & Huents_cap & Huents) & %Hok & %Hokt)".
    { rewrite /own_unstable. iFrame. }
    iDestruct ("Hlback" with "Huf") as "Hl".
    destruct ok.
    - (* the unstable suffix covers [i] *)
      assert (Hin : (uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset')
                     ≤ uint.Z i <
                     uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset')
                     + Z.of_nat (length uents))%Z) by (apply Hok; done).
      wp_auto.
      iApply ("HΦ" $! t interface.nil).
      iSplitL; first reseal_raftLog.
      iEval (rewrite bi.sep_assoc). iSplitR; last by iLeft.
      iPureIntro. split; [split; [intros _; lia | done] | intros _].
      destruct (Hokt eq_refl) as (e & He & ->).
      eapply (plog_term_at_lookup _ _ _
                (length sents + Z.to_nat (uint.Z i
                   - uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset')))%nat).
      { rewrite lookup_app_r; [|lia]. rewrite -He. f_equal. lia. }
      { lia. }
    - assert (Hnotin : ¬ (uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset')
                          ≤ uint.Z i <
                          uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset')
                          + Z.of_nat (length uents))%Z).
      { intros Hc. apply Hok in Hc. done. }
      wp_auto.
      iAssert (own_raftLog l (logstate.mk prev sents uents lcm lap))
        with "[Hl HStorage Huents Huents_cap]" as "Hlog".
      { reseal_raftLog. }
      wp_apply (wp_raftLog__firstIndex _ (logstate.mk prev sents uents lcm lap) with "[$Hlog]") as "%fi [Hlog %Hfi]". logstate_simpl.
      destruct (bool_decide (uint.Z (word.add i (W64 1)) < uint.Z fi)%Z) eqn:Hb1.
      + (* below the compaction boundary: [ErrCompacted] *)
        wp_auto.
        iApply ("HΦ" $! (W64 0) errCompacted).
        iFrame "Hlog". iEval (rewrite bi.sep_assoc). iSplitR; last (iRight; iLeft; iExact "ErrCompacted").
        iPureIntro. apply bool_decide_eq_true in Hb1.
        split; [split; [ intros Hc; exfalso; by apply HErrCompacted | intros Hr; exfalso; word ]
               | intros Hc; exfalso; by apply HErrCompacted ].
      + wp_auto.
        wp_apply (wp_raftLog__lastIndex _ (logstate.mk prev sents uents lcm lap) with "[$Hlog]") as "%li [Hlog %Hli]". logstate_simpl.
        destruct (bool_decide (uint.Z li < uint.Z i)%Z) eqn:Hb2.
        * (* past the last entry: [ErrUnavailable] *)
          wp_auto.
          iApply ("HΦ" $! (W64 0) errUnavailable).
          iFrame "Hlog". iEval (rewrite bi.sep_assoc). iSplitR; last (iRight; iRight; iExact "ErrUnavailable").
          iPureIntro. apply bool_decide_eq_true in Hb2.
          split; [split; [ intros Hc; exfalso; by apply HErrUnavailable
                         | intros Hr; exfalso; word ]
                 | intros Hc; exfalso; by apply HErrUnavailable ].
        * (* in range, and not in the unstable window: ask the [Storage] *)
          wp_auto.
          apply bool_decide_eq_false in Hb1, Hb2.
          assert (Hrange : (uint.Z prev.(raft.entryID.index') ≤ uint.Z i ≤
                            uint.Z prev.(raft.entryID.index')
                            + Z.of_nat (length sents))%Z).
          { split; first word. lia. }
          clear Hnotin Hnw Hok Hokt Hoffset Hnosnap Hstok Happlied Hcommitted
                Hidx Hnowrap HnoConfChange Hb1 Hb2 Hfi Hli Hcm Hap.
          iClear "HisStorage HLI HFI HT HE HB HSnap Hl_logger Hu_logger".
          clear lv isv fi li stored Hstored Hstored_eq.
          iNamed "Hlog".
          iEval (rewrite /own_raftLog_core /=) in "Hcore". iNamed "Hcore". wp_auto.
          iAssert (is_Storage lv.(raft.raftLog.storage')) as "#Hsto".
          { iExact "HisStorage". }
          iDestruct "Hsto" as (isv)
            "(%Hstok & #HLI & #HFI & #HT & #HE & #HB & #HSnap)".
          rewrite Hstok /=.
          pose proof (prefix_length _ _ Hstored) as Hstlen.
          wp_apply ("HT" $! prev stored i with "[$HStorage]").
          { iPureIntro. lia. }
          iIntros (t2) "[%Ht2 HStorage]".
          wp_auto.
          iApply ("HΦ" $! t2 interface.nil).
          iSplitL; first reseal_raftLog.
          iEval (rewrite bi.sep_assoc). iSplitR; last by iLeft.
          iPureIntro. split; [split; [intros _; lia | done] | intros _].
          by eapply term_at_visible.
  Qed.

End RaftLogTermProof.
