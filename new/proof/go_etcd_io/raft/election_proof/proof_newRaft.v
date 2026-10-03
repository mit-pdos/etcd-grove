Require Export New.proof.go_etcd_io.raft.election_proof.postulates_newRaft.

Module NewRaftProof (P : NEWRAFT_POSTULATES) : NEWRAFT.
Import P.

  Lemma wp_newRaft : wp_newRaft_body.
  Proof.
    intros_ambient.
    intros c cv lok si prev ents ss hs cs voters dqv
      Hvalid Hlok Hsto HmaxInfl Hpv Hcq Hdpf Hidx Hncc Hss Hhs Happ Hvne Hvnd Hv0 Hcs1 Hcs2 Hcs3 Hal.
    pose proof Hvalid as (HvID & HvID1 & HvID2 & Hticks & HvSt & HvInfl & HvIB & HvLog & HvRO).
    wp_start as "(Hc & #Hlg0 & #HisSto & HSto & #HInit)".
    wp_auto.
    wp_apply (P.wp_Config__validate _ _ Hvalid with "[$Hc]") as "%cv' (Hc & %Hpres)".
    destruct Hpres as (HpID & HpET & HpHT & HpSt & HpAp & HpMI & HpCQ & HpPV & HpDPF & HpLg).
    rewrite HpSt Hsto HpLg Hlok.
    wp_apply (P.wp_newLogWithSize _ _ _ _ _ _ lok Hidx Hncc Hss eq_refl with "[$HisSto $HSto $Hlg0]") as "%l %lv (Hl & %Hlv & Hcore)".
    destruct Hlv as (Hlvst & Hlvcm & Hlvap).
    try wp_auto.
    rewrite HpSt Hsto /=.
    iEval (rewrite /own_raftLog_core) in "Hcore".
    iDestruct "Hcore" as (sprev stored ss') "(%Hlidx & %Hlnowrap & #HisSto' & HSto & %Hlstore &
      #Hlsnap & %Hloffset & Huents & Huents_cap & %Hlncc & %Hlapplied & %Hlpapplied &
      %Hlcommitted & %Hlssnap & #Hllg & #Hulg)".
    destruct Hlstore as (Hsp & Hlstored & Hlstored_eq). subst sprev.
    rewrite -(Hlstored_eq eq_refl).
    iEval (rewrite Hlvst) in "HSto".
    wp_apply ("HInit" with "[$HSto]"). iIntros "HSto Hvoters".
    iAssert (own_raftLog l (logstate.mk prev ents [] prev.(raft.entryID.index')
                              prev.(raft.entryID.index') None))
      with "[Hl HSto Huents Huents_cap]" as "HL".
    { iApply (own_raftLog_intro with "Hl HisSto HSto Hlsnap Huents Huents_cap Hllg Hulg");
        try done. all: rewrite ?Hlvap ?Hlvcm;
        first [done | (split_and!; done) | (split; lia) | (intros; lia)]. }
    try wp_auto.
    wp_apply P.wp_MakeProgressTracker as "%tv0 %v0 (%Htv0 & Hv0 & Hvotes & Hprs0)".
    destruct Htv0 as (Htv0mi & Htv0mb & Htv0arr & Htv0l & Htv0ln & Htv0al).
    try wp_auto.
    wp_apply P.wp_newReadOnly as "%ro Hro".
    try wp_auto.
    wp_apply wp_alloc. iIntros (r) "Hr". try wp_auto.
    wp_apply P.wp_traceInitState. try wp_auto.
    wp_apply (P.wp_raftLog__lastEntryID with "[$HL]") as "%lastID [HL _]".
    try wp_auto.
    assert (0 ≤ sint.Z tv0.(tracker.ProgressTracker.MaxInflight') < 2 ^ 62)%Z as Hmi.
    { rewrite Htv0mi HpMI. lia. }
    iMod (own_map_persist with "Hprs0") as "#Hprs0".
    wp_apply (P.wp_confchange_Restore
                {| confchange.Changer.Tracker' := tv0;
                   confchange.Changer.LastIndex' := lastID.(raft.entryID.index') |}
                _ voters dqv v0 Hvne Hv0 Hcs1 Hcs2 Hcs3 Hmi
                Htv0arr Htv0l Htv0ln with "[$Hvoters $Hv0 $Hprs0]")
      as "%cfgv %prsm %prs %vref %vm (Hvoters & Hv0 & _ & %Hcfgv & Hvref & %Hvm & Hprsm & %Hprs & Hprogs)".
    destruct Hcfgv as (Hcfgarr & Hcfgl & Hcfgln & Hcfgal).
    try wp_auto.
    (* the struct, over the empty configuration: its tracker is the empty
       one [MakeProgressTracker] built, and its log is at the state
       [newLogWithSize] built.  It holds no [Progress] yet, so [prvals] is
       empty. *)
    set cfgs := (list_to_set voters : gset w64).
    set ls0 := logstate.mk prev ents [] prev.(raft.entryID.index')
                 prev.(raft.entryID.index') None.
    set s0 := nstate.mk (W64 0) (W64 0) (W64 0) role.Follower ∅ [] func.nil ∅ l
                ls0 ∅.
    iDestruct (own_tracker_empty tv0 v0 Htv0arr Htv0l Htv0ln Htv0al Hmi
                 with "Hv0 Hvotes Hprs0") as "Htrk0".
    iAssert (own_raft_misc slice.nil ro slice.nil) with "[Hro]" as "Hmisc".
    { rewrite /own_raft_misc. iExists []. iFrame "Hro".
      iSplitL; [iApply own_slice_nil|]. iSplitL; [iApply own_slice_cap_nil|].
      iSplitL; [iApply own_slice_nil|iApply own_slice_cap_nil]. }
    iDestruct (own_raft_phys_intro ∅ _ cv.(raft.Config.ID') s0 _ [] [] lok with
      "Hr Hlg0 Htrk0 HL [] [] [] [] Hmisc []") as "Hphys".
    all: try done.
    1-5: simpl; rewrite ?HpID ?HpPV ?HpDPF ?HpCQ ?HpLg ?HpET; try done; lia.
    1,3: iApply own_slice_nil.
    1,2: iApply own_slice_cap_nil.
    1: iApply outbox_rel_nil.
    (* the configuration [Restore] built, as [switchToConfig] installs it *)
    iMod (own_map_persist with "Hprsm") as "#Hprsm".
    iDestruct (own_slice_len with "Hvoters") as %[Hvlen Hvlen'].
    assert (Z.of_nat (size cfgs) < 2 ^ 63)%Z as Hcsz.
    { rewrite /cfgs size_list_to_set //. word. }
    iAssert (own_config cfgs cfgv prsm prs) with "[Hvref Hprogs]" as "Hcfg".
    { rewrite /own_config. iExists vref, vm. iFrame "Hvref Hprsm Hprogs".
      iPureIntro. split_and!; done. }
    wp_apply (P.wp_raft__switchToConfig _ _ _ _ s0 cfgv prsm prs
                ltac:(done) with "[$Hphys $Hcfg]")
      as "%cs2 %xs2 %pvs1 (Hphys & Hcs2v & %Hxs2 & %Hcs2l)".
    destruct Hcs2l as (Hc2a & Hc2b & Hc2c & Hc2al).
    try wp_auto.
    assert (voters ≡ₚ xs2) as Hperm.
    { rewrite Hxs2 /cfgs elements_list_to_set //. }
    wp_apply (P.wp_assertConfStatesEquivalent _ cs cs2 voters xs2 dqv (DfracOwn 1)
                Hperm Hcs1 Hcs2 Hcs3 Hc2a Hc2b Hc2c ltac:(rewrite Hal Hc2al //)
                with "[$Hvoters $Hcs2v]") as "[Hvoters Hcs2v]".
    try wp_auto.
    (* [if !IsEmptyHardState(hs) { r.loadState(hs) }]: both arms end at the
       same struct state [s1] and log state [ls1], so the rest of the proof
       is done once, for both. *)
    set ls1 := logstate.mk prev ents [] (committed_after prev hs)
                 prev.(raft.entryID.index') None.
    set s1 := s0 <| nstate.progress := prs |> <| nstate.prvals := pvs1 |>
                 <| nstate.term := hs.(raftpb.HardState.Term') |>
                 <| nstate.vote := hs.(raftpb.HardState.Vote') |>
                 <| nstate.logst := ls1 |>.
    wp_bind (if: _ then _ else _)%E.
    iApply (wp_wand _ _ _
              (λ v, ⌜ v = execute_val ⌝ ∗ own_raft_phys cfgs r cv.(raft.Config.ID') s1 ∗
                    hs_ptr ↦ hs ∗ r_ptr ↦ r)%I
              with "[Hphys hs r]").
    { wp_apply P.wp_IsEmptyHardState.
      destruct (decide (hs_empty hs)) as [Hemp|Hnemp].
      - rewrite bool_decide_eq_true_2; last exact Hemp.
        wp_auto. iFrame "hs r". iSplitR; first done.
        iApply (own_raft_phys_eq with "Hphys").
        rewrite /s1 /ls1 /committed_after bool_decide_eq_true_2; last done.
        destruct Hemp as (HT & HV & _). rewrite HT HV //.
      - rewrite bool_decide_eq_false_2; last exact Hnemp.
        wp_auto.
        assert (uint.Z (log_last ls0)
                = uint.Z prev.(raft.entryID.index') + Z.of_nat (length ents))%Z as Hll.
        { rewrite /log_last /ls0 /=.
          pose proof (word.unsigned_range prev.(raft.entryID.index')).
          rewrite word.unsigned_of_Z_nowrap; lia. }
        wp_apply (P.wp_raft__loadState _ _ _ (s0 <| nstate.progress := prs |> <| nstate.prvals := pvs1 |>) hs
                    ltac:(assert ((s0 <| nstate.progress := prs |> <| nstate.prvals := pvs1 |>).(nstate.logst) = ls0)
                            as -> by done;
                          rewrite Hll /ls0 /=; specialize (Hhs Hnemp); lia)
                    with "[$Hphys]") as "Hphys".
        try wp_auto. iFrame "hs r". iSplitR; first done.
        iApply (own_raft_phys_eq with "Hphys").
        rewrite /s1 /ls1 /committed_after bool_decide_eq_false_2 //. }
    iIntros (v) "(-> & Hphys & hs & r)".
    try wp_auto.
    iClear "HInit Hvoters Hcs2v".
    (* [if c.Applied > 0 { raftlog.appliedTo(c.Applied, 0) }], likewise *)
    set ap := if decide (cv.(raft.Config.Applied') = W64 0)
              then prev.(raft.entryID.index') else cv.(raft.Config.Applied').
    set ls2 := logstate.mk prev ents [] (committed_after prev hs) ap None.
    set s2 := s1 <| nstate.logst := ls2 |>.
    wp_bind (if: _ then _ else _)%E.
    iApply (wp_wand _ _ _
              (λ v, ⌜ v = execute_val ⌝ ∗ own_raft_phys cfgs r cv.(raft.Config.ID') s2 ∗
                    c_ptr ↦ c ∗ c ↦ cv' ∗ raftlog_ptr ↦ l)%I
              with "[Hphys c Hc raftlog]").
    { rewrite HpAp.
      destruct (decide (cv.(raft.Config.Applied') = W64 0)) as [Ha0|Ha0].
      - rewrite bool_decide_eq_false_2; [|rewrite Ha0; word]. wp_auto.
        iFrame "c Hc raftlog". iSplitR; first done.
        iApply (own_raft_phys_eq with "Hphys").
        rewrite /s2 /ls2 /ap ?decide_True //.
      - rewrite bool_decide_eq_true_2; [|word]. wp_auto.
        (* [raftlog] is [r.raftLog]: the log, through the accessor *)
        iDestruct (own_raft_phys_log_at with "Hphys") as "[HL Hlogback]".
        wp_apply (P.wp_raftLog__appliedTo l ls1 cv'.(raft.Config.Applied') (W64 0)
                    ltac:(rewrite HpAp; destruct Happ as [Happ|Happ]; [done|]; simpl; lia)
                    with "[$HL]") as "HL".
        iDestruct ("Hlogback" with "HL") as "Hphys".
        try wp_auto. iFrame "c Hc raftlog". iSplitR; first done.
        iApply (own_raft_phys_eq with "Hphys").
        rewrite /s2 /ls2 /ap ?decide_False // -HpAp //. }
    iIntros (v) "(-> & Hphys & c & Hc & raftlog)".
    try wp_auto.
    set s1n := s2.
    (* [r.becomeFollower(r.Term, None)] *)
    wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
    rewrite /raft.None'.
    wp_apply (P.wp_raft__becomeFollower _ _ _ s1n s1n.(nstate.term) (W64 0)
                with "[$Hphys]") as "%pvs3 Hphys".
    set s3 := become_follower s1n s1n.(nstate.term) (W64 0) <| nstate.prvals := pvs3 |>.
    try wp_auto.
    (* [r.trk.VoterNodes()] *)
    iDestruct (own_raft_phys_tracker_same _ _ _ s3 with "Hphys")
      as (tv3) "(Htrkf & Htrk3 & Htrkback)".
    wp_apply (P.wp_ProgressTracker__VoterNodes with "[$Htrkf $Htrk3]")
           as "%nsl %nxs (Htrkf & Htrk3 & Hnsl & %Hnxs)".
    iDestruct ("Htrkback" with "Htrkf Htrk3") as "Hphys".
    try wp_auto.
    (* the log line's [nodesStrs] loop; what it builds is never read *)
    iAssert (∃ (k x : w64) (sl' : slice.t) (strs : list go_string),
        "i" ∷ i_ptr ↦ k ∗ "n" ∷ n_ptr ↦ x ∗ "nodesStrs" ∷ nodesStrs_ptr ↦ sl' ∗
        "Hstrs" ∷ sl' ↦* strs ∗
        "Hstrs_cap" ∷ own_slice_cap go_string sl' (DfracOwn 1) ∗
        "Hnsl" ∷ nsl ↦* nxs ∗
        "%Hk" ∷ ⌜ (0 ≤ sint.Z k ≤ Z.of_nat (length nxs))%Z ⌝)%I
      with "[i n nodesStrs Hnsl]" as "IH";
      [ iExists (W64 0), (W64 0), slice.nil, []; iFrame;
        iSplitL; [iApply own_slice_nil|]; iSplitL; [iApply own_slice_cap_nil|];
        iPureIntro; word | ].
    wp_for "IH".
    wp_if_destruct;
      [ iDestruct (own_slice_len with "Hnsl") as %[Hnl Hnl'];
        destruct (lookup_lt_is_Some_2 nxs (Z.to_nat (sint.Z k)) ltac:(word)) as [e He];
        rewrite decide_True; [|word];
        wp_apply (wp_load_slice_index (V:=w64) (t:=go.uint64) nsl (sint.Z k) nxs
                    (DfracOwn 1) e ltac:(word) with "[$Hnsl //]") as "Hnsl";
        try wp_auto;
        wp_apply wp_slice_literal; iSplitR; [done|]; iIntros (?) "[Hargs _]";
        try wp_auto;
        wp_apply (P.wp_fmt_Sprintf with "[$Hargs]") as "%str Hargs";
        try wp_auto;
        wp_apply wp_slice_literal; iSplitR; [done|]; iIntros (?) "[Hsl2 _]";
        try wp_auto;
        wp_apply (wp_slice_append with "[$Hstrs $Hstrs_cap $Hsl2]")
          as "%sl3 (Hstrs & Hstrs_cap & _)";
        try wp_auto;
        wp_for_post;
        iFrame; iPureIntro; word
      | idtac ].
    (* the log line: [r.id], [strings.Join(nodesStrs, ",")], [r.Term], then
       [r.raftLog.committed] and [r.raftLog.applied] through the log *)
    wp_apply (wp_raft_load_id with "Hphys") as "Hphys".
    wp_apply (P.wp_strings_Join with "[$Hstrs]") as "%joined Hstrs".
    try wp_auto.
    wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
    try wp_auto.
    wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
    iDestruct (own_raft_phys_log_same with "Hphys") as "(Hlog3 & Hlogback)".
    iDestruct (own_raftLog_struct with "Hlog3") as (?) "(Hl3 & _ & Hl3back)".
    try wp_auto.
    iDestruct ("Hl3back" with "Hl3") as "Hlog3".
    iDestruct ("Hlogback" with "Hlog3") as "Hphys".
    wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
    iDestruct (own_raft_phys_log_same with "Hphys") as "(Hlog3 & Hlogback)".
    iDestruct (own_raftLog_struct with "Hlog3") as (?) "(Hl3 & _ & Hl3back)".
    try wp_auto.
    iDestruct ("Hl3back" with "Hl3") as "Hlog3".
    iDestruct ("Hlogback" with "Hlog3") as "Hphys".
    wp_raft_log.
    iApply ("HΦ" $! r s3). iFrame "Hphys".
    (* [becomeFollower(r.Term, None)] keeps the term, so [reset] keeps the
       vote: the state is the persisted [HardState]'s *)
    iPureIntro. rewrite /s3.
    split; first (apply nstate_wf_prvals, nstate_wf_become_follower).
    rewrite /become_follower /reset_to. cbn [nstate.term nstate.vote nstate.lead
      nstate.role nstate.votes nstate.outbox nstate.prvals set nstate.settable].
    rewrite decide_True //.
  Qed.

End NewRaftProof.
