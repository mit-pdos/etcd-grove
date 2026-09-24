Require Export New.proof.go_etcd_io.raft.election_proof.postulates_newRaft.

Module NewRaftProof (P : NEWRAFT_POSTULATES) : NEWRAFT.
Import P.

  Lemma wp_newRaft : wp_newRaft_body.
  Proof.
    intros_ambient.
    intros c cv lok si prev ents hs cs voters dqv
      Hvalid Hlok Hsto HmaxInfl Hpv Hcq Hidx Hncc Hhs Happ Hvne Hvnd Hv0 Hcs1 Hcs2 Hcs3 Hal.
    pose proof Hvalid as (HvID & HvID1 & HvID2 & Hticks & HvSt & HvInfl & HvIB & HvLog & HvRO).
    wp_start as "(Hc & #Hlg0 & #HisSto & HSto & #HInit)".
    wp_auto.
    wp_apply (P.wp_Config__validate _ _ Hvalid with "[$Hc]") as "%cv' (Hc & %Hpres)".
    destruct Hpres as (HpID & HpET & HpHT & HpSt & HpAp & HpMI & HpCQ & HpPV & HpLg).
    rewrite HpSt Hsto HpLg Hlok.
    wp_apply (P.wp_newLogWithSize _ _ _ _ _ Hidx Hncc with "[$HisSto $HSto]") as "%l %lv (Hl & %Hlv & Hcore)".
    destruct Hlv as (Hlvst & Hlvcm & Hlvap).
    try wp_auto.
    rewrite HpSt Hsto /=.
    iEval (rewrite /own_raftLog_core) in "Hcore".
    iDestruct "Hcore" as "(%Hlidx & %Hlnowrap & #HisSto' & HSto & %Hloffset &
      Huents & Huents_cap & %Hlnosnap & %Hlncc & %Hlapplied & %Hlcommitted)".
    iEval (rewrite Hlvst) in "HSto".
    wp_apply ("HInit" with "[$HSto]"). iIntros "HSto Hvoters".
    iAssert (own_raftLog l (logstate.mk prev ents [] prev.(raft.entryID.index')
                              prev.(raft.entryID.index') None))
      with "[Hl HSto Huents Huents_cap]" as "HL".
    { iApply own_raftLog_unfold. iExists lv. iFrame "Hl". iSplitR; [done|].
      iSplitR; [done|]. rewrite /own_raftLog_core Hlvst. iFrame "∗#%". }
    try wp_auto.
    wp_apply P.wp_MakeProgressTracker as "%tv0 %v0 (%Htv0 & Hv0 & Hvotes & Hprs0)".
    destruct Htv0 as (Htv0mi & Htv0mb & Htv0arr & Htv0l & Htv0ln & Htv0al).
    try wp_auto.
    wp_apply P.wp_newReadOnly as "%ro Hro".
    try wp_auto.
    wp_apply wp_alloc. iIntros (r) "Hr". try wp_auto.
    wp_apply P.wp_traceInitState. try wp_auto.
    wp_apply (P.wp_raftLog__lastEntryID with "[$HL]") as "%lastID HL"; first done.
    try wp_auto.
    assert (0 ≤ sint.Z tv0.(tracker.ProgressTracker.MaxInflight') < 2 ^ 62)%Z as Hmi.
    { rewrite Htv0mi HpMI. lia. }
    wp_apply (P.wp_confchange_Restore
                {| confchange.Changer.Tracker' := tv0;
                   confchange.Changer.LastIndex' := lastID.(raft.entryID.index') |}
                _ voters dqv v0 Hvne Hv0 Hcs1 Hcs2 Hcs3 Hmi
                Htv0arr Htv0l Htv0ln with "[$Hvoters $Hv0 $Hprs0]")
      as "%cfgv %prsm %prs %vref %vm (Hvoters & _ & _ & %Hcfgv & Hvref & %Hvm & Hprsm & %Hprs & Hprogs)".
    destruct Hcfgv as (Hcfgarr & Hcfgl & Hcfgln & Hcfgal).
    try wp_auto.
    (* the struct, with the tracker and the log on loan *)
    set cfgs := (list_to_set voters : gset w64).
    set s0 := nstate.mk (W64 0) (W64 0) (W64 0) role.Follower ∅ [] func.nil prs l
                (Some tv0).
    iPoseProof (own_raftLog_unless_lent tv0 l) as "Hnolog".
    iPoseProof (own_tracker_unless_lent cfgs tv0 ∅ prs) as "Hnotrk".
    iAssert (own_raft_misc slice.nil ro slice.nil) with "[Hro]" as "Hmisc".
    { rewrite /own_raft_misc. iExists [], []. iFrame "Hro".
      iSplitL; [iApply own_slice_nil|]. iSplitL; [iApply own_slice_cap_nil|].
      iSplitL; [iApply own_slice_nil|iApply own_slice_cap_nil]. }
    iDestruct (own_raft_phys_intro cfgs _ cv.(raft.Config.ID') s0 _ [] [] lok with
      "Hr Hlg0 Hnotrk Hnolog [] [] [] [] Hmisc") as "Hphys".
    all: try done.
    1-4: simpl; rewrite ?HpID ?HpPV ?HpCQ ?HpLg ?HpET; try done; lia.
    1,3: iApply own_slice_nil.
    1,2: iApply own_slice_cap_nil.
    (* the new tracker, as [switchToConfig] will install it *)
    iMod (own_map_persist with "Hprsm") as "#Hprsm".
    iDestruct (own_slice_len with "Hvoters") as %[Hvlen Hvlen'].
    assert (Z.of_nat (size cfgs) < 2 ^ 63)%Z as Hcsz.
    { rewrite /cfgs size_list_to_set //. word. }
    assert (cfgs ≠ ∅) as Hcne.
    { rewrite /cfgs. destruct voters as [|v vs]; [done|]. set_solver. }
    set tv' := tv0 <| tracker.ProgressTracker.Config' := cfgv |>
                   <| tracker.ProgressTracker.Progress' := prsm |>.
    iAssert (own_tracker cfgs tv' ∅ prs) with "[Hvotes Hprogs Hvref]" as "Htrkn".
    { rewrite /own_tracker. iExists vref, vm, ∅, ∅. simpl.
      iFrame "Hvotes Hprsm Hprogs Hvref". rewrite Hcfgl Hcfgln.
      repeat (iSplitR; [first [iPureIntro; done | iLeft; done] |]).
      iPureIntro. done. }
    wp_apply (P.wp_raft__switchToConfig _ _ _ s0 tv0 cfgv prsm ∅ prs eq_refl
                ltac:(done) with "[$Hphys $Htrkn]")
      as "%cs2 %xs2 (Hphys & Htrkn & Hcs2v & %Hxs2 & %Hcs2l)".
    destruct Hcs2l as (Hc2a & Hc2b & Hc2c & Hc2al).
    try wp_auto.
    assert (voters ≡ₚ xs2) as Hperm.
    { rewrite Hxs2 /cfgs elements_list_to_set //. }
    wp_apply (P.wp_assertConfStatesEquivalent _ cs cs2 voters xs2 dqv (DfracOwn 1)
                Hperm Hcs1 Hcs2 Hcs3 Hc2a Hc2b Hc2c ltac:(rewrite Hal Hc2al Hcfgal //)
                with "[$Hvoters $Hcs2v]") as "[Hvoters Hcs2v]".
    try wp_auto.
    (* [if !IsEmptyHardState(hs) { r.loadState(hs) }]: both arms end at the
       same struct state [s1] and log state [ls1], so the rest of the proof
       is done once, for both. *)
    set s1 := s0 <| nstate.lent := Some tv' |>
                 <| nstate.term := hs.(raftpb.HardState.Term') |>
                 <| nstate.vote := hs.(raftpb.HardState.Vote') |>.
    set ls1 := logstate.mk prev ents [] (committed_after prev hs)
                 prev.(raft.entryID.index') None.
    wp_bind (if: _ then _ else _)%E.
    iApply (wp_wand _ _ _
              (λ v, ⌜ v = execute_val ⌝ ∗ own_raft_phys cfgs r cv.(raft.Config.ID') s1 ∗
                    own_raftLog l ls1 ∗ hs_ptr ↦ hs ∗ r_ptr ↦ r)%I
              with "[Hphys HL hs r]").
    { wp_apply P.wp_IsEmptyHardState.
      destruct (decide (hs_empty hs)) as [Hemp|Hnemp].
      - rewrite bool_decide_eq_true_2; last exact Hemp.
        wp_auto. iFrame "hs r". iSplitR; first done. iSplitL "Hphys".
        + destruct Hemp as (HT & HV & _). rewrite /s1 HT HV. iExact "Hphys".
        + rewrite /ls1 /committed_after bool_decide_eq_true_2 //.
      - rewrite bool_decide_eq_false_2; last exact Hnemp.
        wp_auto.
        wp_apply (P.wp_raft__loadState _ _ _ (s0 <| nstate.lent := Some tv' |>) tv'
                    (logstate.mk prev ents [] prev.(raft.entryID.index')
                       prev.(raft.entryID.index') None) hs ltac:(done) eq_refl
                    ltac:(simpl; specialize (Hhs Hnemp); lia)
                    with "[$Hphys $HL]") as "[Hphys HL]".
        try wp_auto. iFrame "hs r". iSplitR; first done. iFrame "Hphys".
        rewrite /ls1 /committed_after bool_decide_eq_false_2 //. }
    iIntros (v) "(-> & Hphys & HL & hs & r)".
    try wp_auto.
    iClear "HInit Hvoters Hcs2v".
    (* [if c.Applied > 0 { raftlog.appliedTo(c.Applied, 0) }], likewise *)
    set ap := if decide (cv.(raft.Config.Applied') = W64 0)
              then prev.(raft.entryID.index') else cv.(raft.Config.Applied').
    set ls2 := logstate.mk prev ents [] (committed_after prev hs) ap None.
    wp_bind (if: _ then _ else _)%E.
    iApply (wp_wand _ _ _
              (λ v, ⌜ v = execute_val ⌝ ∗ own_raftLog l ls2 ∗
                    c_ptr ↦ c ∗ c ↦ cv' ∗ raftlog_ptr ↦ l)%I
              with "[HL c Hc raftlog]").
    { rewrite HpAp.
      destruct (decide (cv.(raft.Config.Applied') = W64 0)) as [Ha0|Ha0].
      - rewrite bool_decide_eq_false_2; [|rewrite Ha0; word]. wp_auto.
        iFrame "c Hc raftlog". iSplitR; first done.
        rewrite /ls2 /ap. iExact "HL".
      - rewrite bool_decide_eq_true_2; [|word]. wp_auto.
        wp_apply (P.wp_raftLog__appliedTo l ls1 cv'.(raft.Config.Applied') (W64 0) eq_refl
                    ltac:(rewrite HpAp; destruct Happ as [Happ|Happ]; [done|]; simpl; lia)
                    with "[$HL]") as "HL".
        try wp_auto. iFrame "c Hc raftlog". iSplitR; first done.
        rewrite /ls2 /ap -HpAp. iExact "HL". }
    iIntros (v) "(-> & HL & c & Hc & raftlog)".
    try wp_auto.
    (* end the loan: the tracker and the log go back into the struct *)
    iNamed "Hphys".
    iDestruct (own_tracker_unless_lent_eq with "Htrk") as %Htv'.
    iClear "Htrk Hlog".
    try wp_auto.
    iAssert (own_raft_phys cfgs r cv.(raft.Config.ID') (s1 <| nstate.lent := None |>))
      with "[Hr Htrkn HL Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]" as "Hphys";
      [ iApply (own_raft_phys_intro _ _ _ (s1 <| nstate.lent := None |>) with
          "Hr Hlogger [Htrkn] [HL] Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc");
        [ done .. | rewrite Htv'; iExact "Htrkn"
        | rewrite Hlogp; iExists ls2; iFrame "HL"; done ] | ].
    rewrite /raft.None'.
    wp_apply (P.wp_raft__becomeFollower _ _ _ (s1 <| nstate.lent := None |>)
                     rv.(raft.raft.Term') (W64 0) ltac:(done) with "[$Hphys]") as "Hphys".
    set s3 := become_follower (s1 <| nstate.lent := None |>) rv.(raft.raft.Term') (W64 0).
    try wp_auto.
    (* [r.trk.VoterNodes()] *)
    iDestruct "Hphys" as (rv3 msgs3 msgsAA3 lok3) "Hphys".
    iNamedSuffix "Hphys" "3".
    iDestruct (own_tracker_unless_open _ _ _ _ _ ltac:(done) with "Htrk3") as "Htrk3".
    iDestruct (access_strict
               (A := r.[raft.raft.t, "trk"] ↦ rv3.(raft.raft.trk'))
               (A' := r.[raft.raft.t, "trk"] ↦ rv3.(raft.raft.trk'))
               (P := r ↦ rv3) (P' := r ↦ rv3)
               with "Hr3") as "[Htrkf Hrback]".
    wp_apply (P.wp_ProgressTracker__VoterNodes with "[$Htrkf $Htrk3]")
           as "%nsl %nxs (Htrkf & Htrk3 & Hnsl & %Hnxs)".
    iDestruct ("Hrback" with "Htrkf") as "Hr3".
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
    wp_apply (P.wp_strings_Join with "[$Hstrs]") as "%joined Hstrs".
    iDestruct (own_raftLog_unless_open _ _ ltac:(done) with "Hlog3") as (ls3) "[%Hpg3 Hlog3]".
    iDestruct (own_raftLog_struct with "Hlog3") as (lv3) "(Hl3 & _ & Hl3back)".
    try wp_auto.
    wp_apply wp_slice_literal. iSplitR; first done. iIntros (?) "[? _]".
    try wp_auto. rewrite Hlok3. try wp_auto.
    wp_apply (wp_Logger__logf with "Hlogger3"); first solve_log_method.
    try wp_auto.
    iDestruct ("Hl3back" with "Hl3") as "Hlog3".
    iDestruct (own_raftLog_unless_close _ _ _ ltac:(done) with "Hlog3 [//]") as "Hlog3".
    iDestruct (own_tracker_unless_close _ _ _ _ _ ltac:(done) with "Htrk3") as "Htrk3".
    iApply ("HΦ" $! r s3).
    iSplitL.
    { iApply (own_raft_phys_intro _ _ _ s3 with
        "Hr3 Hlogger3 Htrk3 Hlog3 Hmsgs3 Hmsgs_cap3 HmsgsAA3 HmsgsAA_cap3 Hmisc3"); done. }
    (* [becomeFollower(r.Term, None)] keeps the term, so [reset] keeps the
       vote: the state is the persisted [HardState]'s *)
    iPureIntro. rewrite /s3 Hterm.
    split; first (apply nstate_wf_become_follower; done).
    rewrite /become_follower /reset_to. cbn [nstate.term nstate.vote nstate.lead
      nstate.role nstate.votes nstate.outbox set nstate.settable].
    rewrite decide_True //.
  Qed.

End NewRaftProof.
