Require Export New.proof.go_etcd_io.raft.election_proof.postulates_MajorityConfig__Slice.

Module MajorityConfigSliceProof (P : MAJORITYCONFIG__SLICE_POSTULATES) : MAJORITYCONFIG__SLICE.
Import P.

  Lemma wp_MajorityConfig__Slice : wp_MajorityConfig__Slice_body.
  Proof.
    intros_ambient.
    intros m ids.
    wp_start as "Hm".
    wp_auto.
    iDestruct "Hm" as "[[%Hnil %Hids]|Hm]".
    { (* the nil set: the range is a pure step, and [sl] stays nil *)
      subst m ids. wp_auto.
      iPoseProof (own_slice_nil (V:=w64) (DfracOwn 1)) as "Hsl0".
      wp_apply (P.wp_slices_Sort with "[$Hsl0]") as "%xs (Hsl & %Hxs & _)".
      iApply "HΦ". iFrame "Hsl". iSplitR; first (iLeft; done).
      iSplitL; first iApply own_slice_cap_nil.
      iPureIntro. rewrite dom_empty_L elements_empty. by symmetry. }
    set (Pmap := (λ (keys : list w64) (i : Z),
      ∃ (sl' : slice.t) (x : w64),
        "%Hi" ∷ ⌜ 0 ≤ i ⌝ ∗
        "sl" ∷ sl_ptr ↦ sl' ∗
        "Hsl" ∷ sl' ↦* take (Z.to_nat i) keys ∗
        "Hsl_cap" ∷ own_slice_cap w64 sl' (DfracOwn 1) ∗
        "id" ∷ id_ptr ↦ x)%I).
    wp_apply (wp_map_for_range Pmap with "Hm").
    iIntros (keys) "(%Hkset & %Hklen & %Hknodup)".
    iSplitL "sl id".
    { rewrite /Pmap. iExists slice.nil, (W64 0). rewrite take_0. iFrame.
      iSplitR; first done. iSplitL; [iApply own_slice_nil|iApply own_slice_cap_nil]. }
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
    iIntros "HP Hm". rewrite /Pmap. iNamed "HP".
    rewrite Nat2Z.id -Hklen firstn_all.
    wp_auto.
    wp_apply (P.wp_slices_Sort with "[$Hsl]") as "%xs (Hsl & %Hxs & _)".
    iApply "HΦ". iFrame "Hsl Hsl_cap". iSplitL "Hm"; first (iRight; done).
    iPureIntro. rewrite -Hkset elements_list_to_set //.
  Qed.

End MajorityConfigSliceProof.
