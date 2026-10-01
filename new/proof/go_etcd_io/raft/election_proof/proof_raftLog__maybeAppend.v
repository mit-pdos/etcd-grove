Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__maybeAppend.

(** Pure facts about [plog_find_conflict] the proof needs: it is [0]
    exactly when every entry matches (for a batch with no index [0]), and
    otherwise it is the index of the first entry that does not. *)
Local Lemma find_conflict_cases (b : raft.entryID.t) (es ents : list raftpb.Entry.t) :
  (plog_find_conflict b es ents = W64 0 ∧
   Forall (λ e, plog_matches b es (ent_id e)) ents) ∨
  (∃ (k : nat) e, ents !! k = Some e ∧
     plog_find_conflict b es ents = e.(raftpb.Entry.Index') ∧
     ¬ plog_matches b es (ent_id e) ∧
     (∀ (j : nat) e', (j < k)%nat → ents !! j = Some e' → plog_matches b es (ent_id e'))).
Proof.
  induction ents as [|e ents IH]; simpl.
  - left. split; [done | constructor].
  - case_decide as Hm.
    + destruct IH as [[H0 Hall] | (k & e' & Hk & Hci & Hnm & Hbefore)].
      * left. split; [done | by constructor].
      * right. exists (S k), e'. split_and!; [done | done | done |].
        intros j e'' Hj Hj'. destruct j as [|j]; simpl in Hj'.
        -- by injection Hj' as <-.
        -- apply (Hbefore j); [lia | done].
    + right. exists 0%nat, e. split_and!; [done | done | done |].
      intros j e' Hj. lia.
Qed.

(** [log_truncate_append] moves only the entry lists. *)
Local Lemma log_truncate_append_fields (ls : logstate.t) (ents : list raftpb.Entry.t) :
  (log_truncate_append ls ents).(logstate.prev) = ls.(logstate.prev) ∧
  (log_truncate_append ls ents).(logstate.committed) = ls.(logstate.committed) ∧
  (log_truncate_append ls ents).(logstate.applied) = ls.(logstate.applied).
Proof. destruct ents; done. Qed.

(** A matched entry is inside the log. *)
Local Lemma matches_le_last (b : raft.entryID.t) (es : list raftpb.Entry.t) (id : raft.entryID.t) :
  plog_matches b es id →
  (uint.Z b.(raft.entryID.index') ≤ uint.Z id.(raft.entryID.index')
   ≤ plog_last_index_Z b es)%Z.
Proof. rewrite /plog_matches. apply plog_term_at_Some_range. Qed.

Module RaftLogMaybeAppendProof (P : RAFTLOG__MAYBEAPPEND_POSTULATES) : RAFTLOG__MAYBEAPPEND.
Import P.

  Lemma wp_raftLog__maybeAppend : wp_raftLog__maybeAppend_body.
  Proof.
    intros_ambient.
    intros l ls a ents committed Hwf Hnw Hnorm Hci.
    destruct ls as [prev sents uents lcm lap]; logstate_simpl.
    destruct a as [aterm aprev aents]. cbn [raft.logSlice.prev' raft.logSlice.entries'] in *.
    wp_start as "H". iNamed "H". wp_auto.
    iDestruct (own_slice_len with "Hents") as %[Hlen Hlen'].
    iDestruct (own_raftLog_wf with "Hlog") as "[%Hidx Hlog]". logstate_simpl.
    iDestruct (own_raftLog_committed with "Hlog") as "[%Hcmb Hlog]". logstate_simpl.
    iDestruct (own_raftLog_nowrap with "Hlog") as "[%Hnwl Hlog]". logstate_simpl.
    wp_apply (wp_raftLog__matchTerm _ (logstate.mk prev sents uents lcm lap) aprev with "[$Hlog]") as "%b [Hlog %Hb]".
    rewrite /plog_maybe_append. cbv zeta.
    destruct b.
    2:{ (* [a.prev] does not match: [(0, false)] *)
      symmetry in Hb. apply bool_decide_eq_false_1 in Hb.
      wp_auto. rewrite (decide_False (P := plog_matches _ _ _)) //.
      iApply ("HΦ" $! (W64 0) false (logstate.mk prev sents uents lcm lap)). iFrame. done. }
    symmetry in Hb. apply bool_decide_eq_true_1 in Hb.
    cbn [logstate.prev logstate.sents logstate.uents] in Hb.
    rewrite (decide_True (P := plog_matches _ _ _)) //.
    specialize (Hci Hb). cbn [logstate.prev logstate.sents logstate.uents logstate.committed] in Hci.
    pose proof (matches_le_last _ _ _ Hb) as Hprange.
    rewrite /plog_last_index_Z length_app in Hprange.
    wp_auto.
    set (lastnewi := W64 (uint.Z aprev.(raft.entryID.index') + Z.of_nat (length ents))).
    (* [findConflict]: every entry is above [a.prev], hence above [prev] *)
    assert (Forall (λ e, uint.Z prev.(raft.entryID.index') ≤ uint.Z e.(raftpb.Entry.Index'))%Z
              ents) as Hge.
    { apply List.Forall_forall. intros e He.
      apply list_elem_of_In in He. apply list_elem_of_lookup_1 in He as [k Hk].
      specialize (Hwf k e Hk). lia. }
    wp_apply (wp_raftLog__findConflict _ (logstate.mk prev sents uents lcm lap) _ _ ents Hge with "[$Hlog $Hents]")
      as "[Hlog _]".
    set (ci := plog_find_conflict prev (sents ++ uents) ents).
    fold ci in Hci.
    destruct (find_conflict_cases prev (sents ++ uents) ents)
      as [[Hci0 Hall] | (k & e & Hk & Hcie & Hnm & Hbefore)].
    - (* no conflict: the log already has every entry *)
      fold ci in Hci0. rewrite Hci0.
      rewrite bool_decide_eq_true_2 //. wp_auto.
      (* the log reaches [lastnewi] *)
      assert (uint.Z aprev.(raft.entryID.index') + Z.of_nat (length ents)
              ≤ uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
                + Z.of_nat (length uents))%Z as Hreach.
      { destruct (decide (ents = [])) as [->|Hne]; [simpl; lia|].
        destruct (list.last ents) as [el|] eqn:Hl; last (apply last_None in Hl; done).
        rewrite last_lookup in Hl.
        rewrite List.Forall_forall in Hall.
        assert (el ∈ ents) as Hel by (by eapply list_elem_of_lookup_2).
        apply list_elem_of_In in Hel. specialize (Hall el Hel).
        apply matches_le_last in Hall. rewrite /plog_last_index_Z length_app in Hall.
        specialize (Hwf _ _ Hl). simpl in Hall.
        destruct ents; [done|]. simpl in *. lia. }
      change ([go.uint64; go.uint64]) with (replicate 2 go.uint64).
      rewrite func_unfold /minⁱᵐᵖˡ.
      wp_auto.
      assert (word.add aprev.(raft.entryID.index') aents.(slice.len) = lastnewi) as Hlni.
      { apply word.unsigned_inj. rewrite /lastnewi. word. }
      rewrite ?Hlni.
      set (cmin := if decide (uint.Z committed < uint.Z lastnewi)%Z then committed else lastnewi).
      assert (uint.Z cmin ≤ plog_last_index_Z prev (sents ++ uents))%Z as Hcmin.
      { rewrite /cmin /plog_last_index_Z length_app /lastnewi. case_decide; word. }
      case_bool_decide as Hmin; wp_auto.
      all: wp_apply (wp_raftLog__commitTo with "[$Hlog]");
        [ cbn [logstate.prev logstate.sents logstate.uents];
          rewrite /plog_last_index_Z length_app; try (rewrite /lastnewi in Hmin);
          try (rewrite /lastnewi); word
        | iIntros "Hlog" ].
      all: try wp_auto.
      all: iApply "HΦ"; iFrame "Hlog"; iPureIntro.
      all: split_and!; try done.
      all: simpl; rewrite /cmin; rewrite ?Hlni in Hmin |- *; repeat case_decide; try done; word.
    - (* a conflict at [ci = ents[k].Index = a.prev.index + 1 + k] *)
      fold ci in Hcie. pose proof (f_equal uint.Z Hcie) as HcieZ.
      pose proof (Hwf k e Hk) as Hke. rewrite -Hcie in Hke.
      assert (ci ≠ W64 0) as Hcine.
      { intros Hc. rewrite Hc in Hke. word. }
      destruct Hci as [Hc|Hcgt]; [exfalso; by apply Hcine|].
      rewrite (bool_decide_eq_false_2 (ci = W64 0)) //. rewrite bool_decide_eq_false_2 //.
      iDestruct (own_raftLog_struct with "Hlog") as (lv) "(Hl & [%Hcm %Hap] & Hback)".
      cbn [logstate.committed] in Hcm.
      pose proof (f_equal uint.Z Hcm) as HcmZ.
      wp_auto.
      rewrite (bool_decide_eq_false_2 (uint.Z ci ≤ uint.Z lv.(raft.raftLog.committed'))%Z);
        last lia.
      rewrite bool_decide_eq_false_2 //.
      iDestruct ("Hback" with "Hl") as "Hlog".
      wp_auto.
      assert (k < length ents)%nat as Hklt by (by eapply lookup_lt_Some).
      rewrite bool_decide_eq_false_2; last word.
      wp_auto.
      (* [ci <= lastIndex() + 1]: [ents[k-1]] (or [a.prev]) matched *)
      assert (uint.Z ci ≤ uint.Z prev.(raft.entryID.index') + Z.of_nat (length sents)
                          + Z.of_nat (length uents) + 1)%Z as Hcile.
      { destruct k as [|k'].
        - lia.
        - destruct (lookup_lt_is_Some_2 ents k') as [e' He']; [lia|].
          pose proof (Hbefore k' e' ltac:(lia) He') as Hm'.
          apply matches_le_last in Hm'. rewrite /plog_last_index_Z length_app in Hm'.
          specialize (Hwf k' e' He'). simpl in Hm'. lia. }
      (* the batch from the conflict on: [a.entries[k:]] *)
      replace (word.sub ci (word.add aprev.(raft.entryID.index') (W64 1))) with (W64 k)
        by (apply word.unsigned_inj; word).
      iDestruct (own_slice_split_all (W64 k) with "Hents") as "[_ #Hdrop]"; first word.
      iDestruct (own_slice_cap_wf with "Hcap") as %Hcapwf.
      iDestruct (own_slice_cap_slice _ (W64 k) with "Hcap") as "Hcap'"; first word.
      replace (sint.nat (W64 k)) with k by word.
      set (ents2 := drop k ents).
      assert (ents2 !! 0%nat = Some e) as He2 by (rewrite /ents2 lookup_drop Nat.add_0_r //).
      iAssert (if log_adopts (logstate.mk prev sents uents lcm lap) ents2
               then ⌜ DfracDiscarded = DfracDiscarded ⌝ ∗
                    own_slice_cap raftpb.Entry.t
                      (slice.slice aents raftpb.Entry.t (W64 k) aents.(slice.len)) (DfracOwn 1)
               else True)%I with "[Hcap']" as "Hadopt".
      { destruct (log_adopts (logstate.mk prev sents uents lcm lap) ents2); [by iFrame|done]. }
      try wp_auto.
      rewrite (decide_True (P := (0 ≤ sint.Z (W64 k) ≤ sint.Z aents.(slice.len)
                                    ≤ sint.Z aents.(slice.cap))%Z)); last word.
      wp_auto.
      wp_apply (wp_raftLog__append _ (logstate.mk prev sents uents lcm lap) ents2 _ _
                  ltac:(intros e0 He0; rewrite He2 in He0; injection He0 as <-;
                        simpl; split_and!;
                        [ lia | lia
                        | intros j ej Hj; rewrite /ents2 lookup_drop in Hj;
                          pose proof (Hwf _ _ Hj); lia
                        | rewrite /ents2 length_drop; lia ])
                  ltac:(by apply Forall_drop)
                  with "[$Hlog $Hdrop $Hadopt]")
        as "%li (Hlog & _ & %Hsplit & %Hli)".
      try wp_auto.
      pose proof (log_truncate_append_fields (logstate.mk prev sents uents lcm lap) ents2)
        as (Hp1 & Hc1 & Ha1).
      cbn [logstate.prev logstate.committed logstate.applied] in Hp1, Hc1, Ha1.
      set (ls1 := log_truncate_append (logstate.mk prev sents uents lcm lap) ents2).
      (* the new log reaches exactly [lastnewi] *)
      assert (uint.Z prev.(raft.entryID.index') + Z.of_nat (length ls1.(logstate.sents))
              + Z.of_nat (length ls1.(logstate.uents))
              = uint.Z aprev.(raft.entryID.index') + Z.of_nat (length ents))%Z as Hlast1.
      { assert (length (ls1.(logstate.sents) ++ ls1.(logstate.uents))
                = length (plog_truncate_append prev (sents ++ uents) ents2)) as HL
          by (rewrite Hsplit; done).
        rewrite /ents2 (drop_S _ _ _ Hk) /plog_truncate_append in HL.
        rewrite !length_app length_take /= length_drop length_app in HL.
        lia. }
      change ([go.uint64; go.uint64]) with (replicate 2 go.uint64).
      rewrite func_unfold /minⁱᵐᵖˡ.
      wp_auto.
      assert (word.add aprev.(raft.entryID.index') aents.(slice.len) = lastnewi) as Hlni.
      { apply word.unsigned_inj. rewrite /lastnewi. word. }
      rewrite ?Hlni.
      set (cmin := if decide (uint.Z committed < uint.Z lastnewi)%Z then committed else lastnewi).
      assert (uint.Z cmin ≤ plog_last_index_Z ls1.(logstate.prev)
                              (ls1.(logstate.sents) ++ ls1.(logstate.uents)))%Z as Hcmin.
      { rewrite /cmin /plog_last_index_Z length_app /lastnewi.
        rewrite Hp1. case_decide; word. }
      case_bool_decide as Hmin; wp_auto.
      all: wp_apply (wp_raftLog__commitTo with "[$Hlog]");
        [ rewrite Hp1 /plog_last_index_Z length_app; try (rewrite /lastnewi in Hmin);
          try (rewrite /lastnewi); word
        | iIntros "Hlog" ].
      all: try wp_auto.
      all: iApply "HΦ"; iFrame "Hlog"; iPureIntro.
      all: split_and!; try done; simpl.
      all: try (rewrite Hp1; done).
      all: try (rewrite Ha1; done).
      all: try (rewrite decide_False; [|exact Hcine];
                replace (Z.to_nat (uint.Z ci - uint.Z aprev.(raft.entryID.index') - 1)) with k
                  by lia;
                exact Hsplit).
      all: rewrite Hc1 /cmin; rewrite ?Hlni in Hmin |- *; repeat case_decide; try done; word.
  Qed.

End RaftLogMaybeAppendProof.
