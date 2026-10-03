Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__restore.

Module RaftRestoreProof (P : RAFT__RESTORE_POSTULATES) : RAFT__RESTORE.
Import P.

  (** The body's exits in order ([raft__restoreⁱᵐᵖˡ]):

      - [Index <= committed]: [false];
      - [state != StateFollower]: dead ([s.role = Follower]);
      - the [found] search over [[Voters; Learners; VotersOutgoing]]: [id]
        is among the voters ([snap_scope], [id ∈ cfg]), so the inner loop
        breaks in the first set and the outer loop right after it; the
        [!found] arm is dead;
      - [matchTerm(id)]: [lastEntryID], an [Infof], [commitTo(Index)] (in
        range: [Index] has a term in the log) and [false];
      - otherwise [raftLog.restore(s)]; the tracker replaced by the empty
        one [MakeProgressTracker] builds -- [own_raft_phys] at the empty
        configuration, as in [newRaft] ([own_raft_phys_reconfig],
        [own_tracker_empty]; the tally was already empty, [s.votes = ∅]);
        [confchange.Restore] on it, its [v0] read back out of the empty
        tracker; then [switchToConfig] back to [cfg] and
        [assertConfStatesEquivalent]; [lastEntryID], an [Infof] and [true]. *)
  Lemma wp_raft__restore : wp_raft__restore_body.
  Proof.
    intros_ambient.
    intros cfg r id s sv voters Hrole Hvotes Hin Hscope.
    destruct Hscope as (Hperm & H0 & Hcl & Hcvo & Hcln & Hcal & Hidx61).
    wp_start as "H". iNamed "H". wp_auto.
    (* [s.Metadata.Index <= r.raftLog.committed] *)
    wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
    iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hlogback]".
    iDestruct (own_raftLog_struct with "Hlog") as (lv) "(Hl & %Hlv & Hlb)".
    wp_auto.
    iDestruct ("Hlb" with "Hl") as "Hlog".
    iDestruct ("Hlogback" with "Hlog") as "Hphys".
    destruct Hlv as [Hcm _]. rewrite Hcm.
    destruct (decide (uint.Z sv.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.Index')
                      ≤ uint.Z s.(nstate.logst).(logstate.committed))) as [Hst|Hst].
    { (* obsolete *)
      rewrite bool_decide_eq_true_2 //. wp_auto.
      iApply "HΦ". iFrame "Hphys". iPureIntro. left. split_and!; [exact Hst|done|done]. }
    rewrite bool_decide_eq_false_2 //. wp_auto.
    (* [r.state != StateFollower]: a follower *)
    wp_apply (wp_raft_load_state with "Hphys") as "Hphys".
    rewrite Hrole. rewrite bool_decide_eq_true_2 //. wp_auto.
    (* the [found] search over [[Voters; Learners; VotersOutgoing]] *)
    wp_apply wp_slice_literal. iSplitR; first done. iIntros (rsl) "[Hrsl _]".
    replace (sint.nat (W64 0)) with 0%nat by done.
    rewrite /go.array_literal_size /= /Z.max /= /Z.add /=.
    wp_auto.
    (* the outer loop runs once: [id] is among the voters, so the inner
       loop breaks with [found], and so does the outer one *)
    iAssert (∃ (k : w64) (st : slice.t),
       "i" ∷ i_ptr ↦ k ∗ "set" ∷ set_ptr ↦ st ∗ "found" ∷ found_ptr ↦ false ∗
       "%Hk" ∷ ⌜ k = W64 0 ⌝)%I with "[i set found]" as "IH".
    { iExists (W64 0), slice.nil. iFrame. done. }
    wp_for "IH".
    subst k.
    wp_if_destruct; last first.
    { exfalso. word. }
    set (V := sv.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.ConfState')
                .(raftpb.ConfState.Voters')).
    wp_apply (wp_load_slice_index (V:=slice.t) (t:=go.SliceType go.uint64)
                _ (sint.Z (W64 0)) _ (DfracOwn 1) V with "[$Hrsl]") as "Hrsl";
      try first [ word | iPureIntro; reflexivity | tc_solve | done ].
    (* the inner loop's own counter clashes with the outer one's *)
    wp_alloc j_ptr as "j". wp_auto.
    iDestruct (own_slice_len with "Hvoters") as %[Hvlen Hvlen'].
    assert (id ∈ voters) as Hidv.
    { rewrite Hperm. by apply elem_of_elements. }
    iAssert (∃ (k2 x : w64),
       "j" ∷ j_ptr ↦ k2 ∗ "id" ∷ id_ptr ↦ x ∗ "found" ∷ found_ptr ↦ false ∗
       "%Hk2" ∷ ⌜ (0 ≤ sint.Z k2 ≤ Z.of_nat (length voters))%Z ∧
                  id ∉ take (Z.to_nat (sint.Z k2)) voters ⌝)%I
      with "[j id found]" as "IH2".
    { iExists (W64 0), (W64 0). iFrame. iPureIntro. split; [word|].
      rewrite (_ : Z.to_nat (sint.Z (W64 0)) = 0%nat); last word.
      rewrite take_0. apply not_elem_of_nil. }
    wp_for "IH2".
    destruct Hk2 as [Hk2b Hk2n].
    wp_if_destruct; last first.
    { (* the voters ran out without [id]: impossible *)
      exfalso. apply Hk2n.
      rewrite take_ge; [exact Hidv|]. word. }
    destruct (lookup_lt_is_Some_2 voters (Z.to_nat (sint.Z k2)) ltac:(word)) as [y Hy].
    case_decide as Hdec; [clear Hdec | exfalso; apply Hdec; word].
    wp_apply (wp_load_slice_index (V:=w64) (t:=go.uint64)
                V (sint.Z k2) voters DfracDiscarded y with "[$Hvoters]") as "_";
      try first [ word | iPureIntro; exact Hy | tc_solve | done ].
    wp_apply (wp_raft_load_id with "Hphys") as "Hphys".
    destruct (decide (y = id)) as [->|Hne]; last first.
    { (* not this one: next *)
      rewrite bool_decide_eq_false_2 //. wp_auto.
      wp_for_post.
      iFrame. iPureIntro. split; [word|].
      rewrite (_ : Z.to_nat (sint.Z (word.add k2 (W64 1))) = S (Z.to_nat (sint.Z k2))); last word.
      rewrite (take_S_r _ _ y Hy) elem_of_app list_elem_of_singleton.
      intros [?|?]; [done|congruence]. }
    (* found: break the inner loop, then the outer one *)
    rewrite bool_decide_eq_true_2 //. wp_auto.
    wp_for_post.
    wp_for_post.
    (* [matchTerm(id)] *)
    wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
    iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hlogback]".
    wp_apply (wp_raftLog__matchTerm _ _ (snap_id sv) with "[$Hlog]") as "%b [Hlog %Hb]".
    iDestruct ("Hlogback" with "Hlog") as "Hphys".
    destruct (decide (plog_matches s.(nstate.logst).(logstate.prev)
                        (s.(nstate.logst).(logstate.sents) ++ s.(nstate.logst).(logstate.uents))
                        (snap_id sv))) as [Hm|Hnm].
    - (* the log has the snapshot's last entry: fast-forward the commit *)
      rewrite Hb (bool_decide_eq_true_2 _ Hm). wp_auto.
      wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
      iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hlogback]".
      wp_apply (wp_raftLog__lastEntryID with "[$Hlog]") as "%last [Hlog _]".
      iDestruct ("Hlogback" with "Hlog") as "Hphys".
      (* the [Infof]: [r.id], [r.raftLog.committed], the two ids *)
      wp_apply (wp_raft_load_id with "Hphys") as "Hphys".
      wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
      iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hlogback]".
      iDestruct (own_raftLog_struct with "Hlog") as (lv2) "(Hl & _ & Hlb)".
      wp_auto.
      iDestruct ("Hlb" with "Hl") as "Hlog".
      iDestruct ("Hlogback" with "Hlog") as "Hphys".
      wp_raft_log.
      (* [commitTo(Index)]: in range, the log has a term at [Index] *)
      pose proof (plog_term_at_Some_range _ _ _ _ Hm) as [_ Hle].
      wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
      iDestruct (own_raft_phys_log_at with "Hphys") as "[Hlog Hlogback]".
      wp_apply (wp_raftLog__commitTo _ _ (snap_id sv).(raft.entryID.index') Hle
                  with "[$Hlog]") as "Hlog".
      iDestruct ("Hlogback" with "Hlog") as "Hphys".
      try wp_auto.
      iApply "HΦ". iSplitL.
      { iApply (own_raft_phys_eq with "Hphys").
        rewrite /plog_commit_to decide_True; last (simpl; lia).
        by destruct s. }
      iPureIntro. right; left. split_and!; [simpl; lia|exact Hm|done|done].
    - rewrite Hb (bool_decide_eq_false_2 _ Hnm). wp_auto.
      (* [r.raftLog.restore(s)] *)
      wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
      iDestruct (own_raft_phys_log_at with "Hphys") as "[Hlog Hlogback]".
      wp_apply (wp_raftLog__restore _ _ sv voters with "[$Hlog $Hvoters]") as "Hlog".
      { simpl. lia. }
      { simpl. lia. }
      iDestruct ("Hlogback" with "Hlog") as "Hphys".
      (* the tracker replaced by the empty one, the log used meanwhile *)
      iDestruct (own_raft_phys_retrack _ ∅ with "Hphys")
        as (tv) "(Htrkf & Htrk & Hlf & Hlog & Hback)".
      iDestruct (own_tracker_maxinflight with "Htrk") as "[%Hmi _]".
      wp_auto.
      wp_apply wp_MakeProgressTracker as "%tv0 %v0 (%Htv0 & Hv0 & Hvotes & Hprs0)".
      destruct Htv0 as (Htv0mi & Htv0mb & Htv0arr & Htv0l & Htv0ln & Htv0al).
      try wp_auto.
      wp_apply (wp_raftLog__lastIndex with "[$Hlog]") as "%li [Hlog _]".
      (* [confchange.Restore]: the empty tracker, the voters-only [ConfState] *)
      iMod (own_map_persist with "Hprs0") as "#Hprs0".
      assert (0 ≤ sint.Z tv0.(tracker.ProgressTracker.MaxInflight') < 2 ^ 62)%Z as Hmi0.
      { rewrite Htv0mi. exact Hmi. }
      assert (voters ≠ []) as Hvne.
      { intros ->. by apply not_elem_of_nil in Hidv. }
      assert (W64 0 ∉ voters) as Hv0n.
      { rewrite Hperm. intros Hz%elem_of_elements. done. }
      wp_apply (wp_confchange_Restore
                  {| confchange.Changer.Tracker' := tv0;
                     confchange.Changer.LastIndex' := li |}
                  _ voters DfracDiscarded v0 Hvne Hv0n Hcvo Hcl Hcln Hmi0
                  Htv0arr Htv0l Htv0ln with "[$Hvoters $Hv0 $Hprs0]")
        as "%cfgv %prsm %prs %vref %vm (_ & Hv0 & _ & %Hcfgv & Hvref & %Hvm & Hprsm & %Hprs & Hprogs)".
      destruct Hcfgv as (Hcfgarr & Hcfgl & Hcfgln & Hcfgal).
      try wp_auto.
      (* the struct, re-sealed over the empty configuration *)
      iDestruct (own_tracker_empty tv0 v0 Htv0arr Htv0l Htv0ln Htv0al Hmi0
                   with "Hv0 Hvotes Hprs0") as "Htrk0".
      iDestruct ("Hback" with "Hlf Htrkf Htrk0 Hlog") as "Hphys".
      (* [assertConfStatesEquivalent(r.logger, cs, r.switchToConfig(cfg, trk))] *)
      wp_apply (wp_raft_load_logger with "Hphys") as (lok0) "[Hphys #Hlg0]".
      try wp_auto.
      assert (list_to_set voters = cfg) as Hcfgeq.
      { rewrite Hperm list_to_set_elements_L //. }
      iDestruct (own_slice_len with "Hvoters") as %[Hvl1 Hvl2].
      assert (Z.of_nat (size (list_to_set voters : gset w64)) < 2 ^ 63)%Z as Hcsz.
      { rewrite size_list_to_set; [word|]. rewrite Hperm. apply NoDup_elements. }
      iMod (own_map_persist with "Hprsm") as "#Hprsm".
      iAssert (own_config (list_to_set voters) cfgv prsm prs) with "[Hvref Hprogs]" as "Hcfg".
      { rewrite /own_config. iExists vref, vm. iFrame "Hvref Hprsm Hprogs".
        iPureIntro. split_and!; done. }
      wp_apply (wp_raft__switchToConfig _ _ _ _ _ cfgv prsm prs with "[$Hphys $Hcfg]")
        as "%cs2 %xs2 %pvs1 (Hphys & Hcs2v & %Hxs2 & %Hcs2l)".
      { simpl. rewrite Hrole. done. }
      destruct Hcs2l as (Hc2a & Hc2b & Hc2c & Hc2al).
      assert (voters ≡ₚ xs2) as Hperm2.
      { rewrite Hxs2 elements_list_to_set //. by rewrite Hperm; apply NoDup_elements. }
      wp_apply (wp_assertConfStatesEquivalent _ _ cs2 voters xs2 DfracDiscarded (DfracOwn 1)
                  Hperm2 Hcvo Hcl Hcln Hc2a Hc2b Hc2c ltac:(rewrite Hcal Hc2al //)
                  with "[$Hvoters $Hcs2v]") as "[_ _]".
      rewrite Hcfgeq.
      wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
      iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hlogback]".
      wp_apply (wp_raftLog__lastEntryID with "[$Hlog]") as "%last [Hlog _]".
      iDestruct ("Hlogback" with "Hlog") as "Hphys".
      wp_apply (wp_raft_load_id with "Hphys") as "Hphys".
      wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
      iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hlogback]".
      iDestruct (own_raftLog_struct with "Hlog") as (lv3) "(Hl & _ & Hlb)".
      wp_auto.
      iDestruct ("Hlb" with "Hl") as "Hlog".
      iDestruct ("Hlogback" with "Hlog") as "Hphys".
      wp_raft_log.
      iApply "HΦ". iSplitL.
      { iApply (own_raft_phys_eq with "Hphys"). reflexivity. }
      iPureIntro. right; right. split_and!; [simpl; lia|exact Hnm|done|].
      exists prs, pvs1. destruct s; simpl in *. subst. reflexivity.
  Qed.

End RaftRestoreProof.
