Require Export New.proof.go_etcd_io.raft.election_proof.postulates_ProgressTracker__ConfState.

Module ProgressTrackerConfStateProof (P : PROGRESSTRACKER__CONFSTATE_POSTULATES) : PROGRESSTRACKER__CONFSTATE.
Import P.

  Lemma wp_ProgressTracker__ConfState : wp_ProgressTracker__ConfState_body.
  Proof.
    intros_ambient.
    intros cfg trk tv votes prs.
    wp_start as "[Htrk Hown]". iNamed "Hown".
    wp_auto.
    (* [Voters[0].Slice()]: the receiver is a pointer into the tracker's
       [JointConfig] array.  Split the array field out of [trk ↦ tv] and
       element 0 out of the array. *)
    iDestruct (access_strict
                 (A := trk.[tracker.ProgressTracker.t, "Config"]
                         ↦ tv.(tracker.ProgressTracker.Config'))
                 (A' := trk.[tracker.ProgressTracker.t, "Config"]
                         ↦ tv.(tracker.ProgressTracker.Config'))
                 (P := trk ↦ tv) (P' := trk ↦ tv) with "Htrk") as "[Hcf Htrkback]".
    iDestruct (access_strict
                 (A := (trk.[tracker.ProgressTracker.t, "Config"]).[tracker.Config.t, "Voters"]
                         ↦ tv.(tracker.ProgressTracker.Config').(tracker.Config.Voters'))
                 (A' := (trk.[tracker.ProgressTracker.t, "Config"]).[tracker.Config.t, "Voters"]
                         ↦ tv.(tracker.ProgressTracker.Config').(tracker.Config.Voters'))
                 (P := trk.[tracker.ProgressTracker.t, "Config"]
                         ↦ tv.(tracker.ProgressTracker.Config'))
                 (P' := trk.[tracker.ProgressTracker.t, "Config"]
                         ↦ tv.(tracker.ProgressTracker.Config'))
                 with "Hcf") as "[Hvf Hcfback]".
    iDestruct (array_acc _ 0 with "Hvf") as "[Hc0 Hcback]".
    { done. }
    { rewrite Hvoters_arr. done. }
    wp_method_call. wp_call. wp_auto.
    wp_apply (P.wp_MajorityConfig__Slice with "[Hvoters]") as "%sl0 %xs0 (Hvoters & Hsl0 & _ & %Hxs0)".
    { iRight. iFrame. }
    iDestruct ("Hcback" with "Hc0") as "Hvf".
    (* element 1, the nil outgoing config *)
    iDestruct (array_acc _ 1 with "Hvf") as "[Hc1 Hcback]".
    { done. }
    { rewrite list_lookup_insert_ne // Hvoters_arr. done. }
    try wp_auto. wp_method_call. wp_call. wp_auto.
    wp_apply (P.wp_MajorityConfig__Slice map.nil ∅ with "[]")
      as "%sl1 %xs1 (_ & Hsl1 & _ & %Hxs1)".
    { iLeft. done. }
    iDestruct ("Hcback" with "Hc1") as "Hvf".
    assert (array.mk 2 (<[Z.to_nat 1:=map.nil]>
              (<[Z.to_nat 0:=voters_ref]>
                 (array.arr tv.(tracker.ProgressTracker.Config').(tracker.Config.Voters'))))
            = tv.(tracker.ProgressTracker.Config').(tracker.Config.Voters')) as Harr.
    { destruct tv.(tracker.ProgressTracker.Config').(tracker.Config.Voters') as [vs].
      simpl in *. subst vs. done. }
    rewrite Harr.
    iDestruct ("Hcfback" with "Hvf") as "Hcf".
    iDestruct ("Htrkback" with "Hcf") as "Htrk".
    try wp_auto.
    wp_apply (P.wp_MajorityConfig__Slice with "[$Hlearners]")
      as "%sl2 %xs2 (Hlearners & Hsl2 & _ & %Hxs2)".
    try wp_auto.
    wp_apply (P.wp_MajorityConfig__Slice with "[$HlearnersNext]")
      as "%sl3 %xs3 (HlearnersNext & Hsl3 & _ & %Hxs3)".
    try wp_auto.
    destruct Hno_learners as [-> ->].
    rewrite dom_empty_L elements_empty in Hxs1 Hxs2 Hxs3.
    apply Permutation_nil_r in Hxs1, Hxs2, Hxs3. subst xs1 xs2 xs3.
    iDestruct (own_slice_len with "Hsl1") as %[Hl1 Hl1'].
    iDestruct (own_slice_len with "Hsl2") as %[Hl2 Hl2'].
    iDestruct (own_slice_len with "Hsl3") as %[Hl3 Hl3'].
    iDestruct "Hvoters" as "[[%Hvn %Hve]|Hvoters]".
    { exfalso. subst voters. apply Hcfg_ne. rewrite -Hvoters_dom dom_empty_L //. }
    iApply ("HΦ" $! _ xs0). iFrame "Htrk Hsl0".
    iSplitL "Hvotes Hprogs Hvoters Hlearners HlearnersNext".
    { rewrite /own_tracker. iExists voters_ref, voters, ∅, ∅.
      iFrame "Hvotes Hprs Hprogs Hvoters Hlearners HlearnersNext".
      repeat (iSplitR; [iPureIntro; done|]). iPureIntro. done. }
    iPureIntro. split; first (rewrite -Hvoters_dom //).
    cbn [raftpb.ConfState.VotersOutgoing' raftpb.ConfState.Learners'
         raftpb.ConfState.LearnersNext' raftpb.ConfState.AutoLeave'].
    cbn [length] in Hl1, Hl2, Hl3.
    split_and!; [word|word|word|done].
  Qed.

End ProgressTrackerConfStateProof.
