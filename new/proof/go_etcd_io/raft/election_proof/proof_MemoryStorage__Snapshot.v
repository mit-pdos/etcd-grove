Require Export New.proof.go_etcd_io.raft.election_proof.postulates_MemoryStorage__Snapshot.

Module MemoryStoragePublicSnapshotProof (P : MEMORYSTORAGE__PUBLIC_SNAPSHOT_POSTULATES) : MEMORYSTORAGE__PUBLIC_SNAPSHOT.
Import P.

  Lemma wp_MemoryStorage__Snapshot : wp_MemoryStorage__Snapshot_body.
  Proof.
    intros_ambient.
    intros ms prev ents ss esu.
    wp_start as "[H #Hesu]". iNamed "H". iNamed "Hms".
    wp_apply wp_with_defer as "%defer defer".
    simpl subst. wp_auto.
    iAssert (is_pkg_init sync) as "#Hsync"; first iPkgInit.
    wp_bind. wp_method_call. wp_call.
    wp_apply (wp_Mutex__Lock with "[$Hmu]") as "[Hlocked Hinv]".
    iNamedSuffix "Hinv" "_inv". iNamed "Hfields_inv".
    iCombine "Hgs Hgs_inv" gives %[_ Heq]. simplify_eq.
    wp_auto.
    iDestruct "Hvoters" as "#Hvoters".
    iAssert (memstorage_fields ms prev0 ents0 (snap_id snap)) with "[HhardState Hsnapshot Hents_f Hents HcallStats]" as "Hf".
    { iExists _, _, _, _, _, _. iFrame "∗#%". iPureIntro. reflexivity. }
    wp_bind. wp_method_call. wp_call.
    wp_apply (wp_Mutex__Unlock with "[$Hmu $Hlocked Hgs_inv Hf]").
    { iNext. iExists prev0, ents0, (snap_id snap). iFrame. }
    iApply "HΦ".
    iSplitL.
    { iExists γ. iFrame "∗#%". }
    iRight. iSplit.
    { iPureIntro. split_and!; [done | done | ].
      rewrite /snap_id /= in Hss. exact Hss. }
    iExists voters. iFrame "#".
  Qed.

End MemoryStoragePublicSnapshotProof.
