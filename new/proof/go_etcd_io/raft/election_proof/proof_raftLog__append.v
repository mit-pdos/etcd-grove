Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__append.


(** The split of the new entry list: the stable part below [e0.Index],
    then the unstable part below it, then the batch. *)
Local Lemma truncate_append_split (prev : raft.entryID.t) (sents uents ents : list raftpb.Entry.t)
    (e0 : raftpb.Entry.t) :
  ents !! 0%nat = Some e0 →
  (uint.Z prev.(raft.entryID.index') < uint.Z e0.(raftpb.Entry.Index'))%Z →
  take (Z.to_nat (uint.Z e0.(raftpb.Entry.Index') - uint.Z prev.(raft.entryID.index') - 1)) sents
  ++ (take (Z.to_nat (uint.Z e0.(raftpb.Entry.Index') - uint.Z prev.(raft.entryID.index') - 1
                      - Z.of_nat (length sents))) uents ++ ents)
  = plog_truncate_append prev (sents ++ uents) ents.
Proof.
  intros H0 Hgt. destruct ents as [|e ents']; [done|]. injection H0 as ->.
  rewrite /plog_truncate_append take_app -app_assoc.
  replace (Z.to_nat (uint.Z e0.(raftpb.Entry.Index') - uint.Z prev.(raft.entryID.index') - 1
                     - Z.of_nat (length sents)))
    with (Z.to_nat (uint.Z e0.(raftpb.Entry.Index') - uint.Z prev.(raft.entryID.index') - 1)
          - length sents)%nat by lia.
  done.
Qed.

Module RaftLogAppendProof (P : RAFTLOG__APPEND_POSTULATES) : RAFTLOG__APPEND.
Import P.

  (** Two exits.  An empty batch returns [lastIndex()] with the log
      untouched.  Otherwise the [Panicf] is dead by the [committed]
      premise, [truncateAndAppend] gets the [unstable] field (its offset
      is [prev.index + |sents| + 1], [Hoffset]), and the log is re-sealed at
      [log_truncate_append]: same [stored], the visible stable part cut at
      [e0.Index] when the batch starts inside it. *)
  Lemma wp_raftLog__append : wp_raftLog__append_body.
  Proof.
    intros_ambient.
    intros l ls ents es dq.
    intros Hpre Hnorm.
    destruct ls as [prev sents uents lcm lap snap]; logstate_simpl.
    wp_start as "H". iNamed "H". wp_auto.
    iDestruct (own_slice_len with "Hes") as %[Hlen Hlen'].
    destruct ents as [|e0 ents'].
    - (* [len(ents) == 0]: the log is untouched and the result is the old
         last index.  The predicate does not have to be opened at all. *)
      simpl in Hlen.
      rewrite bool_decide_eq_true_2; last word.
      wp_auto.
      wp_apply (wp_raftLog__lastIndex _ (logstate.mk prev sents uents lcm lap snap) with "[$Hlog]") as "%li [Hlog %Hli]". logstate_simpl.
      iApply ("HΦ" $! li). simpl. iFrame.
      iPureIntro. rewrite /plog_truncate_append. split; [done | lia].
    - (* the batch is non-empty: [ents[0]] exists *)
      set (ents := e0 :: ents').
      assert (ents !! 0%nat = Some e0) as He0 by done.
      destruct (Hpre e0 He0) as (Hrange & Hcontig & Hnwb). simpl in Hrange.
      change (length (e0 :: ents')) with (length ents) in Hnwb.
      simpl in Hlen.
      rewrite bool_decide_eq_false_2; last word.
      wp_auto.
      case_decide as Hdec; [clear Hdec | exfalso; apply Hdec; word].
      iDestruct (own_slice_elem_acc 0 e0 es dq ents with "Hes")
        as "[He0 Hesback]"; [ word | exact He0 | ].
      wp_auto.
      iDestruct ("Hesback" with "He0") as "Hes".
      rewrite list_insert_id //.
      (* the [Panicf]: [after = e0.Index - 1 >= committed] *)
      iNamed "Hlog".
      iEval (rewrite /own_raftLog_core /=) in "Hcore".
      iDestruct "Hcore" as (sprev stored) "Hcore". iNamed "Hcore". logstate_simpl.
      pose proof (f_equal uint.Z Hcm) as HcmZ.
      wp_auto.
      rewrite bool_decide_eq_false_2; last word.
      wp_auto.
      (* hand the [unstable] field to [truncateAndAppend] *)
      iDestruct (raftLog_split_unstable with "Hl") as "[Huf Hlback]".
      iPoseProof "Hu_logger" as "Hulgv". iEval (rewrite /is_Logger_val) in "Hulgv".
      iDestruct "Hulgv" as (ulg Hulg) "#Hulgr".
      assert (uint.Z e0.(raftpb.Entry.Index')
              ≤ uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset')
                + Z.of_nat (length uents))%Z as Hle' by lia.
      assert (uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset')
              + Z.of_nat (length uents) < 2^64)%Z as Hnw' by lia.
      (* the two adopt conditions agree *)
      assert (bool_decide (uint.Z e0.(raftpb.Entry.Index')
                             ≤ uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset') ∧
                           uint.Z e0.(raftpb.Entry.Index')
                             ≠ uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset')
                               + Z.of_nat (length uents))%Z
              = log_adopts (logstate.mk prev sents uents lcm lap snap) ents) as Hadopt_eq.
      { rewrite /log_adopts /=. apply bool_decide_ext. rewrite Hoffset. lia. }
      wp_apply (wp_unstable__truncateAndAppend _ _ _ _ _ _ _ _ He0 Hle' Hnw' Hulg
                  with "[Huf Huents Huents_cap $Hes $Hulgr Hadopt]")
        as "%uv' (Hun & %Huv' & Hes)".
      { rewrite /own_unstable. iFrame. rewrite Hadopt_eq. iFrame. }
      rewrite Hadopt_eq.
      iNamed "Hun".
      iDestruct ("Hlback" with "Hu") as "Hl".
      destruct Huv' as (Hoff' & Hsnap' & Hlg').
      (* the new state *)
      set (n := Z.to_nat (uint.Z e0.(raftpb.Entry.Index') - uint.Z prev.(raft.entryID.index') - 1)).
      assert (Z.to_nat (uint.Z e0.(raftpb.Entry.Index')
                        - uint.Z lv.(raft.raftLog.unstable').(raft.unstable.offset'))
              = Z.to_nat (uint.Z e0.(raftpb.Entry.Index') - uint.Z prev.(raft.entryID.index') - 1
                          - Z.of_nat (length sents))) as Hm by lia.
      rewrite Hm.
      set (sents' := take n sents).
      set (uents' := take (Z.to_nat (uint.Z e0.(raftpb.Entry.Index')
                                     - uint.Z prev.(raft.entryID.index') - 1
                                     - Z.of_nat (length sents))) uents ++ ents).
      assert (sents' ++ uents' = plog_truncate_append prev (sents ++ uents) ents) as Hsplit.
      { apply truncate_append_split; [done | lia]. }
      assert (length sents' = Nat.min n (length sents)) as Hls' by (rewrite length_take; lia).
      assert (Z.of_nat (length sents') + Z.of_nat (length uents')
              = uint.Z e0.(raftpb.Entry.Index') - uint.Z prev.(raft.entryID.index') - 1
                + Z.of_nat (length ents))%Z as Hlens'.
      { rewrite /uents' length_app length_take. lia. }
      assert (log_indices_ok prev (sents' ++ uents')) as Hidx'.
      { rewrite Hsplit. eapply plog_wf_truncate_append; [exact Hidx | exact He0 | | ].
        - rewrite /plog_last_index_Z length_app. lia.
        - intros k e Hk. by apply Hcontig. }
      assert (Forall (λ e, e.(raftpb.Entry.Type') = EntryNormal) (sents' ++ uents')) as Hnc'.
      { rewrite /sents' /uents' app_assoc. apply Forall_app. split; [|done].
        apply Forall_app in HnoConfChange as [Hs Hu]. apply Forall_app. split.
        - by apply Forall_take.
        - by apply Forall_take. }
      (* the re-seal's premises, stated at the new struct value *)
      assert (uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents')
              + Z.of_nat (length uents') + 1 < 2^64)%Z as Hnw2.
      { lia. }
      (* the storage relation: the visible stable part is cut, or -- with a
         snapshot pending -- stays empty *)
      assert (log_store_ok snap sprev stored prev sents' uents') as Hst2.
      { destruct snap as [sid|].
        - destruct Hstore as (Hp & Hs & Hsid). split; [done|split; [|done]].
          rewrite /sents' Hs take_nil //.
        - destruct Hstore as (Hp & Hstored & _). split_and!; [done| |].
          + etrans; [apply prefix_take | done].
          + intros Hnil. apply app_eq_nil in Hnil as [_ Hnil]. discriminate Hnil. }
      assert (uint.Z uv'.(raft.unstable.offset')
              = uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents') + 1)%Z as Hoff2.
      { rewrite Hoff'. rewrite /sents' length_take. lia. }
      assert (uint.Z lv.(raft.raftLog.committed')
              ≤ uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents')
                + Z.of_nat (length uents'))%Z as Hcm2 by lia.
      iEval (rewrite -Hlg') in "Hu_logger".
      iEval (rewrite -Hsnap') in "Husnap".
      iAssert (own_raftLog l (logstate.mk prev sents' uents' lcm lap snap))
        with "[Hl HStorage Hents Hents_cap]" as "Hlog".
      { iApply (own_raftLog_intro with
                 "Hl HisStorage HStorage Husnap Hents Hents_cap Hl_logger Hu_logger");
          done. }
      wp_apply (wp_raftLog__lastIndex _ (logstate.mk prev sents' uents' lcm lap snap)
                  with "[$Hlog]") as "%li [Hlog %Hli]". logstate_simpl.
      iApply ("HΦ" $! li). iFrame "Hlog Hes". iPureIntro. split; [exact Hsplit |].
      change (log_truncate_append _ ents) with (logstate.mk prev sents' uents' lcm lap snap).
      cbn [logstate.prev logstate.sents logstate.uents]. lia.
  Qed.

End RaftLogAppendProof.
