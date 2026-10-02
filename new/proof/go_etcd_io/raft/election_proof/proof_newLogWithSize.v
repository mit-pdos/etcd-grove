Require Export New.proof.go_etcd_io.raft.election_proof.postulates_newLogWithSize.

Module NewLogWithSizeProof (P : NEWLOGWITHSIZE_POSTULATES) : NEWLOGWITHSIZE.

  Lemma wp_newLogWithSize : wp_newLogWithSize_body.
  Proof.
    intros_ambient.
    intros st lg maxSize prev ents lok Hidx Hnocc ->.
    wp_start as "(#Hsto & HStorage & #Hlg)".
    iAssert (is_Storage st) as "#Hsto2"; first iExact "Hsto".
    iDestruct "Hsto" as (isv) "(%Hstok & #HLI & #HFI & #HT & #HE & #HB & #HSnap)".
    subst st.
    iDestruct ("HB" with "HStorage") as "[%Hbnd HStorage]".
    wp_auto.
    wp_apply ("HFI" with "HStorage") as "%fi [%Hfi HStorage]".
    try wp_auto.
    wp_apply ("HLI" with "HStorage") as "%li [%Hli HStorage]".
    try wp_auto.
    wp_apply wp_alloc. iIntros (l) "Hl". wp_auto.
    iApply "HΦ". iFrame "Hl".
    iSplitR; first (iPureIntro; simpl; split_and!; [done|apply word.unsigned_inj; word ..]).
    rewrite /own_raftLog_core /= app_nil_r. iExists prev, ents. iFrame "HStorage Hsto2".
    repeat (iSplitR; [ first [ iPureIntro; (done || word || (split_and!; done) || (split; word) || (intros; word))
                             | (rewrite own_snap_None; iPureIntro; done)
                             | iApply own_slice_nil
                             | iApply own_slice_cap_nil
                             | (iExists lok; iFrame "Hlg"; done) ] | ]).
    iExists lok; iFrame "Hlg"; done.
  Qed.

End NewLogWithSizeProof.
