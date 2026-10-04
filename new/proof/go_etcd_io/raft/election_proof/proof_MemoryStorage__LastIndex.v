Require Export New.proof.go_etcd_io.raft.election_proof.postulates_MemoryStorage__LastIndex.

Module MemoryStoragePublicLastIndexProof (P : MEMORYSTORAGE__PUBLIC_LASTINDEX_POSTULATES) : MEMORYSTORAGE__PUBLIC_LASTINDEX.
Import P.

  Lemma wp_MemoryStorage__LastIndex : wp_MemoryStorage__LastIndex_body.
  Proof.
    intros_ambient.
    intros ms prev ents ss.
    wp_start as "H". iNamed "H". iNamed "Hms".
    wp_apply wp_with_defer as "%defer defer".
    simpl subst. wp_auto.
    iAssert (is_pkg_init sync) as "#Hsync"; first iPkgInit.
    wp_bind. wp_method_call. wp_call.
    wp_apply (wp_Mutex__Lock with "[$Hmu]") as "[Hlocked Hinv]".
    iNamedSuffix "Hinv" "_inv". iNamed "Hfields_inv".
    iCombine "Hgs Hgs_inv" gives %[_ Heq]. simplify_eq.
    wp_auto.
    iAssert (memstorage_fields ms prev0 ents0 (snap_id snap)) with "[HhardState Hsnapshot Hvoters Hents_f Hents HcallStats]" as "Hf".
    { iExists _, _, _, _, _, _. iFrame "∗%". iPureIntro. reflexivity. }
    wp_apply (wp_MemoryStorage__lastIndex _ _ _ _ Hbounded with "[$Hf]").
    iIntros "%li [%Hli Hf]".
    wp_auto.
    wp_bind. wp_method_call. wp_call.
    wp_apply (wp_Mutex__Unlock with "[$Hmu $Hlocked Hgs_inv Hf]").
    { iFrame "#". iExists _, _, _. iFrame. }
    iApply "HΦ".
    iSplitR; first done.
    iExists γ. iFrame "∗#%".
  Qed.

End MemoryStoragePublicLastIndexProof.
