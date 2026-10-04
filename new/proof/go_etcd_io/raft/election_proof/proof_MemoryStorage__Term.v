Require Export New.proof.go_etcd_io.raft.election_proof.postulates_MemoryStorage__Term.

Module MemoryStoragePublicTermProof (P : MEMORYSTORAGE__PUBLIC_TERM_POSTULATES) : MEMORYSTORAGE__PUBLIC_TERM.
Import P.

  Lemma wp_MemoryStorage__Term : wp_MemoryStorage__Term_body.
  Proof.
    intros_ambient.
    intros ms prev ents ss i0.
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
    { exfalso. rewrite Hd0 in l. lia. }
    wp_if_destruct.
    { exfalso. rewrite Hd0 in l. clear -l Hrange Hlen Hlen' Hbounded. word. }
    assert (Hn : sint.Z (word.sub i0 dummy.(raftpb.Entry.Index')) =
                 (uint.Z i0 - uint.Z prev0.(raft.entryID.index'))%Z).
    { rewrite Hd0. clear -Hrange Hbounded. word. }
    rewrite Hn.
    assert (Hlt : (Z.to_nat (uint.Z i0 - uint.Z prev0.(raft.entryID.index')) <
                   length (dummy :: ents0))%nat).
    { simpl. lia. }
    destruct (lookup_lt_is_Some_2 (dummy :: ents0) _ Hlt) as [e He].
    iDestruct (own_slice_elem_acc (uint.Z i0 - uint.Z prev0.(raft.entryID.index')) e
                 with "Hents") as "[He1 _]"; [lia|exact He|].
    case_decide as Hdec; last first.
    { exfalso. apply Hdec. clear -Hrange Hlen Hlen' Hbounded. lia. }
    clear Hdec.
    wp_auto.
    assert (Hterm : term_at prev0 ents0 i0 = Some e.(raftpb.Entry.Term')).
    { rewrite /term_at. case_decide as Hi.
      - assert (Z.to_nat (uint.Z i0 - uint.Z prev0.(raft.entryID.index')) = 0%nat)
          as H0 by lia.
        rewrite H0 /= in He. injection He as <-. by rewrite Hd1.
      - replace (Z.to_nat (uint.Z i0 - uint.Z prev0.(raft.entryID.index')))
          with (S (Z.to_nat (uint.Z i0 - uint.Z prev0.(raft.entryID.index') - 1)))
          in He by lia.
        simpl in He. by rewrite He. }
    iAssert (memstorage_fields ms prev0 ents0 (snap_id snap)) with "[HhardState Hsnapshot Hvoters Hents_f HcallStats]" as "Hf".
    { iExists _, _, _, _, _, _. iFrame "∗#%". iPureIntro. reflexivity. }
    wp_bind. wp_method_call. wp_call.
    wp_apply (wp_Mutex__Unlock with "[$Hmu $Hlocked Hgs_inv Hf]").
    { iNext. iExists prev0, ents0, (snap_id snap). iFrame. }
    iApply "HΦ".
    iSplitR; first done.
    iExists γ. iFrame "∗#%".
  Qed.

End MemoryStoragePublicTermProof.
