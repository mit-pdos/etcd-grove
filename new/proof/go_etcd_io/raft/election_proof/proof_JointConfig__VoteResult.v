Require Export New.proof.go_etcd_io.raft.election_proof.postulates_JointConfig__VoteResult.

Module JointConfigVoteResultProof (P : JOINTCONFIG__VOTERESULT_POSTULATES)
  : JOINTCONFIG__VOTERESULT.
Import P.

  (** [H : a = b] between two distinct [quorum.VoteResult] constants is
      absurd; [defs.v]'s [w32_ne] is the same trick one width down.  The
      comparisons themselves are mostly taken by [wp_auto], which reduces
      [bool_decide] between two *syntactically equal* constants on its own;
      only the first test of each path needs [case_bool_decide]. *)
  Ltac w8_absurd H :=
    apply (f_equal uint.Z) in H; vm_compute in H; discriminate.

  (** Both components are asked, and the second is [map.nil] -- an empty
      config, whose result is [VoteWon] by convention -- so the combination
      returns [r1] on all three paths.  The array element reads go through
      [array_acc] ([new/golang/theory/array.v]), exactly as in
      [proof_JointConfig__IDs.v]; [Hvoters_arr] says element 0 is
      [voters_ref] and element 1 is [map.nil]. *)
  Lemma wp_JointConfig__VoteResult : wp_JointConfig__VoteResult_body.
  Proof.
  intros_ambient.
  intros cfg trk tv [votes prs pvs] Hcfg_ne.
  wp_start as "[Htrk Hown]". iNamed "Hown". trk_simpl.
  wp_auto.
  wp_method_call. wp_call. wp_call.
  wp_auto.
  iDestruct (array_acc _ 0 with "c") as "[Hc0 Hcback]".
  { done. }
  { rewrite Hvoters_arr. done. }
  wp_apply (wp_MajorityConfig__VoteResult cfg with "[$Hc0 $Hvotes Hvoters]").
  { iSplitR; first (iPureIntro; exact Hcfg_size).
    iRight. iExists voters. by iFrame. }
  iIntros (r1) "(Hc0 & Hvotes & Hv & %Hr1 & _ & %Hwon1 & %Hlost1)".
  (* the first component is the real voter set, so the [map.nil] disjunct of
     [wp_MajorityConfig__VoteResult]'s postcondition would give [cfg = ∅] *)
  iDestruct "Hv" as "[[_ %Hemp]|(%voters' & %Hvoters'_dom & Hvoters)]";
    first (destruct (Hcfg_ne Hemp)).
  wp_auto.
  (* [c[1]]: the nil component of a simple configuration *)
  iDestruct ("Hcback" with "Hc0") as "c".
  rewrite Hvoters_arr /=.
  iDestruct (array_acc _ 1 with "c") as "[Hc1 Hcback]".
  { done. }
  { done. }
  wp_apply (wp_MajorityConfig__VoteResult ∅ with "[$Hc1 $Hvotes]").
  { iSplitR; first (iPureIntro; rewrite size_empty; lia). by iLeft. }
  iIntros (r2) "(Hc1 & Hvotes & _ & %Hr2 & %Hr2won & _ & _)".
  (* "elections on an empty config win": [r2] is [VoteWon], so the joint
     answer is [r1] on every path *)
  assert (r2 = VoteWon) as -> by (by apply Hr2won).
  iDestruct ("Hcback" with "Hc1") as "c".
  wp_auto.
  destruct Hr1 as [Hrv|[Hrv|Hrv]]; subst r1.
  - (* [r1 == r2]: both won *)
    case_bool_decide as Hcmp; last (destruct (Hcmp eq_refl)). wp_auto.
    iApply ("HΦ" $! VoteWon). iFrame "Htrk".
    iSplitL "Hvotes Hprogs Hvoters Hlearners HlearnersNext".
    { iApply (own_tracker_intro with
    "Hvotes Hprs Hprogs Hvoters Hlearners HlearnersNext"); done. }
    iPureIntro. split_and!; [ by left | by apply Hwon1 | by apply Hlost1 ].
  - (* [r1] lost, [r2] won: the second test fires on [r1] *)
    case_bool_decide as Hcmp; first (w8_absurd Hcmp). wp_auto.
    iApply ("HΦ" $! VoteLost). iFrame "Htrk".
    iSplitL "Hvotes Hprogs Hvoters Hlearners HlearnersNext".
    { iApply (own_tracker_intro with
    "Hvotes Hprs Hprogs Hvoters Hlearners HlearnersNext"); done. }
    iPureIntro. split_and!; [ by right; left | by apply Hwon1 | by apply Hlost1 ].
  - (* [r1] still pending: neither test fires *)
    case_bool_decide as Hcmp; first (w8_absurd Hcmp). wp_auto.
    iApply ("HΦ" $! VotePending). iFrame "Htrk".
    iSplitL "Hvotes Hprogs Hvoters Hlearners HlearnersNext".
    { iApply (own_tracker_intro with
    "Hvotes Hprs Hprogs Hvoters Hlearners HlearnersNext"); done. }
    iPureIntro.
    split_and!; [ by right; right | by apply Hwon1 | by apply Hlost1 ].
  Qed.

End JointConfigVoteResultProof.
