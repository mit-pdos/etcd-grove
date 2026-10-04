Require Export New.proof.go_etcd_io.raft.election_proof.postulates_MemoryStorage__Entries.

Module MemoryStoragePublicEntriesProof (P : MEMORYSTORAGE__PUBLIC_ENTRIES_POSTULATES) : MEMORYSTORAGE__PUBLIC_ENTRIES.
Import P.

  Lemma wp_MemoryStorage__Entries : wp_MemoryStorage__Entries_body.
  Proof.
    intros_ambient.
    intros ms prev ents ss lo hi maxSize.
    wp_start as "[H %Hrange]". iNamed "H". iNamed "Hms".
    wp_apply wp_with_defer as "%defer defer".
    simpl subst. wp_auto.
    iAssert (is_pkg_init sync) as "#Hsync"; first iPkgInit.
    wp_bind. wp_method_call. wp_call.
    wp_apply (wp_Mutex__Lock with "[$Hmu]") as "[Hlocked Hinv]".
    iNamedSuffix "Hinv" "_inv". iNamed "Hfields_inv".
    iCombine "Hgs Hgs_inv" gives %[_ Heq]. simplify_eq.
    wp_auto.
    iDestruct "Hents" as "#Hents".
    iDestruct (own_slice_len with "Hents") as %[Hlen Hlen'].
    simpl in Hlen.
    iDestruct (own_slice_elem_acc 0 dummy with "Hents") as "[He _]"; [lia|done|].
    case_decide as Hdec; last first.
    { exfalso. apply Hdec. clear Hdec Hdummy. word. }
    clear Hdec.
    wp_auto.
    pose proof Hdummy as [Hd0 Hd1].
    wp_if_destruct.
    { exfalso. rewrite Hd0 in l. clear -l Hrange. lia. }
    iAssert (memstorage_fields ms prev0 ents0 (snap_id snap)) with "[HhardState Hsnapshot Hvoters Hents_f HcallStats]" as "Hf".
    { iExists _, _, _, _, _, _. iFrame "∗#%". iPureIntro. reflexivity. }
    wp_apply (wp_MemoryStorage__lastIndex _ _ _ _ Hbounded with "[$Hf]")
      as "%li [%Hli Hf]".
    iClear "Hents He". iNamed "Hf".
    iDestruct "Hents" as "#Hents".
    iDestruct (own_slice_len with "Hents") as %[Hlen2 Hlen2'].
    simpl in Hlen2.
    wp_if_destruct.
    { exfalso. clear -Hli Hrange Hbounded l. word. }
    wp_if_destruct.
    { exfalso. clear -Hlen2 Hrange e. rewrite e in Hlen2. word. }
    iDestruct (own_slice_wf with "Hents") as %Hwf2.
    pose proof Hdummy0 as [Hd0' Hd1'].
    set (lo' := word.sub lo dummy.(raftpb.Entry.Index')).
    set (hi' := word.sub hi dummy.(raftpb.Entry.Index')).
    assert (Hlo' : sint.Z lo' = (uint.Z lo - uint.Z prev0.(raft.entryID.index'))%Z).
    { subst lo'. rewrite Hd0. clear -Hrange Hbounded. word. }
    assert (Hhi' : sint.Z hi' = (uint.Z hi - uint.Z prev0.(raft.entryID.index'))%Z).
    { subst hi'. rewrite Hd0. clear -Hrange Hbounded. word. }
    case_decide as Hdec; last first.
    { exfalso. apply Hdec. clear -Hlo' Hhi' Hrange Hlen2 Hwf2. rewrite Hlo' Hhi'. word. }
    clear Hdec.
    wp_auto.
    set (E0 := subslice (sint.nat lo') (sint.nat hi') (dummy0 :: ents0)).
    assert (HE0 : E0 = drop (Z.to_nat (uint.Z lo - uint.Z prev0.(raft.entryID.index') - 1))
                        (take (Z.to_nat (uint.Z hi - uint.Z prev0.(raft.entryID.index') - 1)) ents0)).
    { subst E0. rewrite /subslice.
      replace (sint.nat lo') with (S (Z.to_nat (uint.Z lo - uint.Z prev0.(raft.entryID.index') - 1))) by (clear -Hlo' Hrange; word).
      replace (sint.nat hi') with (S (Z.to_nat (uint.Z hi - uint.Z prev0.(raft.entryID.index') - 1))) by (clear -Hhi' Hrange; word).
      done. }
    assert (HE0len : length E0 = Z.to_nat (uint.Z hi - uint.Z lo)).
    { rewrite HE0 length_drop length_take. lia. }
    iDestruct (own_slice_slice lo' hi' with "Hents") as "(_ & #Hsub & _)"; first (rewrite Hlo' Hhi'; word).
    wp_apply (wp_limitSize with "[$Hsub]") as "%s1 %nlim ([%Hn1a %Hn1b] & #Hs1 & _)".
    iDestruct (own_slice_len with "Hs1") as %[Hs1len Hs1len'].
    iDestruct (own_slice_wf with "Hs1") as %Hs1wf.
    assert (HE0ne : E0 ≠ []).
    { intros Hc. rewrite Hc in HE0len. simpl in HE0len. lia. }
    specialize (Hn1b HE0ne).
    assert (Hnetake : take nlim E0 ≠ []).
    { intros Hc. assert (length (take nlim E0) = 0)%nat as Hz by (rewrite Hc //).
      rewrite length_take in Hz. lia. }
    case_decide as Hfs; last first.
    { exfalso. apply Hfs. clear -Hs1wf. word. }
    clear Hfs.
    wp_auto.
    iDestruct (own_slice_same_ptr_len s1
                 (slice.full_slice s1 raftpb.Entry.t (W64 0) s1.(slice.len) s1.(slice.len))
                 with "Hs1") as "Hs2".
    { exact Hnetake. }
    { rewrite /= /slice_index_ref /= go.array_index_ref_0 //. }
    { simpl. word. }
    { simpl. word. }
    iAssert (memstorage_fields ms prev0 ents0 (snap_id snap)) with "[HhardState Hsnapshot Hvoters Hents_f HcallStats]" as "Hf".
    { iExists _, _, _, _, _, _. iFrame "∗#%". }
    wp_bind. wp_method_call. wp_call.
    wp_apply (wp_Mutex__Unlock with "[$Hmu $Hlocked Hgs_inv Hf]").
    { iNext. iExists prev0, ents0, (snap_id snap). iFrame. }
    iApply ("HΦ" $! _ (take nlim E0)).
    iFrame "Hs2".
    iSplitR.
    { iPureIntro. split_and!.
      - exact Hnetake.
      - rewrite length_take HE0len. lia.
      - intros e He.
        assert (He0 : e ∈ E0).
        { rewrite -(take_drop nlim E0). apply elem_of_app. by left. }
        rewrite HE0 in He0.
        rewrite -(take_drop (Z.to_nat (uint.Z lo - uint.Z prev0.(raft.entryID.index') - 1))
                    (take (Z.to_nat (uint.Z hi - uint.Z prev0.(raft.entryID.index') - 1)) ents0)).
        apply elem_of_app. by right.
      - simpl. done.
      - rewrite -HE0. apply prefix_take. }
    iExists γ. iFrame "∗#%".
  Qed.

End MemoryStoragePublicEntriesProof.
