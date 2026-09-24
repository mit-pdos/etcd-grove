Require Export New.proof.go_etcd_io.raft.election_proof.postulates_ProgressTracker__VoterNodes.

Module ProgressTrackerVoterNodesProof (P : PROGRESSTRACKER__VOTERNODES_POSTULATES) : PROGRESSTRACKER__VOTERNODES.
Import P.

  Lemma wp_ProgressTracker__VoterNodes : wp_ProgressTracker__VoterNodes_body.
  Proof.
    intros_ambient.
    intros cfg trk tv votes prs.
    wp_start as "[Htrk Hown]".
    wp_auto.
    wp_apply (P.wp_JointConfig__IDs with "[$Htrk $Hown]")
      as "%mref %idm (Htrk & Hown & Hidm & %Hdomidm)".
    iNamed "Hown".
    iAssert (own_tracker cfg tv votes prs)
      with "[Hvotes Hprogs Hvoters Hlearners HlearnersNext]" as "Hown".
    { rewrite /own_tracker. iExists voters_ref, voters, learners, learnersNext.
      iFrame "∗#%". }
    try wp_auto.
    wp_apply (wp_map_len with "Hidm") as "Hidm".
    assert (size idm = size cfg) as Hszidm.
    { rewrite -Hdomidm size_dom //. }
    rewrite Hszidm.
    wp_apply (wp_slice_make3 (V:=w64) (t:=go.uint64))
      as (sl) "(Hsl & Hsl_cap & %Hslcap)"; first word.
    replace (sint.nat (W64 0)) with 0%nat by done. simpl.
    set (Pmap := (λ (keys : list w64) (i : Z),
      ∃ (sl' : slice.t) (x : w64),
        "%Hi" ∷ ⌜ 0 ≤ i ⌝ ∗
        "nodes" ∷ nodes_ptr ↦ sl' ∗
        "Hsl" ∷ sl' ↦* take (Z.to_nat i) keys ∗
        "Hsl_cap" ∷ own_slice_cap w64 sl' (DfracOwn 1) ∗
        "id" ∷ id_ptr ↦ x)%I).
    try wp_auto.
    wp_apply (wp_map_for_range Pmap with "Hidm").
    iIntros (keys) "(%Hkset & %Hklen & %Hknodup)".
    iSplitL "nodes Hsl Hsl_cap id".
    { rewrite /Pmap. iExists sl, (W64 0). rewrite take_0. iFrame.
      iPureIntro. lia. }
    iSplitL "".
    { iIntros "!>" (i key vv) "[%Hkey %Hvv] HP". rewrite /Pmap. iNamed "HP".
      wp_auto.
      wp_apply wp_slice_literal. iSplitR; first done. iIntros "%sl2 [Hsl2 _]".
      wp_auto.
      replace (sint.nat (W64 0)) with 0%nat by done.
      rewrite /go.array_literal_size /= /Z.max /= /Z.add /=.
      wp_apply (wp_slice_append with "[$Hsl $Hsl_cap $Hsl2]")
        as "%sl3 (Hsl & Hsl_cap & _)".
      iRight. iLeft. iSplitR; first done.
      assert (Z.to_nat (i + 1) = S (Z.to_nat i)) as Hsucc.
      { exact (Z2Nat.inj_succ i Hi). }
      assert (take (Z.to_nat (i + 1)) keys = take (Z.to_nat i) keys ++ [key])
        as Htake.
      { rewrite Hsucc. by apply take_S_r. }
      iExists sl3, key. rewrite Htake. iFrame. iPureIntro.
      change (0 <= i + 1)%Z. lia. }
    iIntros "HP _". rewrite /Pmap. iNamed "HP".
    rewrite Nat2Z.id -Hklen firstn_all.
    wp_auto.
    wp_apply (P.wp_slices_Sort with "[$Hsl]") as "%xs (Hsl & %Hxs)".
    try wp_auto.
    iApply "HΦ". iFrame "Htrk Hown Hsl". iPureIntro.
    rewrite -Hxs -Hdomidm -Hkset elements_list_to_set //.
  Qed.

End ProgressTrackerVoterNodesProof.
