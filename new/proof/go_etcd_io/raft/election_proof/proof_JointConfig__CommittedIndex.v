Require Export New.proof.go_etcd_io.raft.election_proof.postulates_JointConfig__CommittedIndex.

Module JointConfigCommittedIndexProof (P : JOINTCONFIG__COMMITTEDINDEX_POSTULATES)
  : JOINTCONFIG__COMMITTEDINDEX.
Import P.

  (** Open [own_tracker]; lend [c[0]] (the voter map) and the progress map
      with its [Progress] objects ([own_progress_map]) to the first
      [MajorityConfig.CommittedIndex], the latter as the indexer's [P];
      then [c[1]], the nil component, whose answer is [MaxUint64]; then
      [min].  The array element reads go through [array_acc], as in
      [proof_JointConfig__VoteResult.v]. *)
  Lemma wp_JointConfig__CommittedIndex : wp_JointConfig__CommittedIndex_body.
  Proof.
  intros_ambient.
  intros cfg trk tv [votes prs pvs].
  wp_start as "(Htrk & Hown)". iNamed "Hown". trk_simpl.
  wp_auto.
  wp_method_call. wp_call. wp_call.
  wp_auto.
  (* the indexer's contract, from [matchAckIndexer.AckedIndex]'s triple *)
  iAssert (is_AckedIndexer
             (interface.mk_ok tracker.matchAckIndexer
                #(tv.(tracker.ProgressTracker.Progress')))
             (own_progress_map tv.(tracker.ProgressTracker.Progress') prs pvs)
             (pvs_acked pvs))%I as "#Hidx".
  { iExists _. iSplit; first done.
    iIntros "!>" (id Ψ) "!> HP HΨ". simpl.
    wp_apply (wp_matchAckIndexer__AckedIndex with "[$HP]") as "HP".
    by iApply "HΨ". }
  iAssert (own_progress_map tv.(tracker.ProgressTracker.Progress') prs pvs)%I
    with "[Hprogs]" as "HP".
  { rewrite /own_progress_map. iFrame "∗#". }
  iDestruct (array_acc _ 0 with "c") as "[Hc0 Hcback]".
  { done. }
  { rewrite Hvoters_arr. done. }
  iAssert (⌜ Z.of_nat (size cfg) < 2 ^ 63 ⌝)%I as "Hsz"; first done.
  (* the voter map is a real map, so the callee's [map.nil] disjunct
     cannot come back for it *)
  iDestruct (own_map_not_nil with "Hvoters") as %Hvnn.
  wp_apply (wp_MajorityConfig__CommittedIndex cfg with "[$Hc0 $Hsz $Hidx $HP Hvoters]").
  { iRight. iExists voters. by iFrame. }
  iIntros (N0) "(Hc0 & Hv & HP & %Hemp0 & %Hq0)".
  iDestruct "Hv" as "[[%Hnil _]|(%voters' & %Hvoters'_dom & Hvoters)]".
  { exfalso. by apply Hvnn. }
  wp_auto.
  (* [c[1]]: the nil component of a simple configuration *)
  iDestruct ("Hcback" with "Hc0") as "c".
  rewrite Hvoters_arr /=.
  iDestruct (array_acc _ 1 with "c") as "[Hc1 Hcback]".
  { done. }
  { done. }
  iAssert (⌜ Z.of_nat (size (∅ : gset w64)) < 2 ^ 63 ⌝)%I as "Hsz1".
  { iPureIntro. rewrite size_empty. lia. }
  wp_apply (wp_MajorityConfig__CommittedIndex ∅ with "[$Hc1 $Hsz1 $Hidx $HP]").
  { by iLeft. }
  iIntros (N1) "(Hc1 & _ & HP & %Hemp1 & _)".
  assert (N1 = W64 (2 ^ 64 - 1)) as -> by (by apply Hemp1).
  iDestruct ("Hcback" with "Hc1") as "c".
  iAssert (own_tracker cfg tv (trk.mk votes prs pvs))
    with "[Hvotes HP Hvoters Hlearners HlearnersNext]" as "Hown".
  { iDestruct "HP" as "(_ & Hprogs)". rewrite /own_tracker.
    iExists voters_ref, voters', learners, learnersNext. iFrame "∗#%". }
  wp_auto.
  (* [min]: [c[0]]'s answer on both exits *)
  case_bool_decide as Hlt; wp_auto.
  - iApply "HΦ". iFrame "Htrk Hown". iPureIntro. split; [exact Hemp0 | exact Hq0].
  - assert (N0 = W64 (2 ^ 64 - 1)) as Heq by word.
    iApply "HΦ". iFrame "Htrk Hown". rewrite -Heq. iPureIntro.
    split; [done | exact Hq0].
  Qed.

End JointConfigCommittedIndexProof.
