Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__snapshot.

Module RaftLogSnapshotProof (P : RAFTLOG__SNAPSHOT_POSTULATES) : RAFTLOG__SNAPSHOT.

  (** Two exits: a pending snapshot is returned by value (its index is
      non-zero, [log_store_ok]); otherwise [Storage.Snapshot]. *)
  Lemma wp_raftLog__snapshot : wp_raftLog__snapshot_body.
  Proof.
    intros_ambient.
    intros l ls esu.
    destruct ls as [prev sents uents lcm lap snap]; logstate_simpl.
    wp_start as "H". iNamed "H".
    iNamed "Hlog".
    iEval (rewrite /own_raftLog_core /=) in "Hcore". iNamed "Hcore".
    iAssert (is_Storage lv.(raft.raftLog.storage')) as "#Hsto".
    { iExact "HisStorage". }
    iDestruct "Hsto" as (isv) "(%Hstok & #HLI & #HFI & #HT & #HE & #HB & #HSnap)".
    wp_auto.
    destruct snap as [sid|].
    - (* the pending snapshot, read through [l.unstable.snapshot] *)
      iPoseProof "Husnap" as "Hus". iEval (rewrite own_snap_Some) in "Hus". iDestruct "Hus" as (sv) "[#Hsv %Hmeta]".
      iDestruct (typed_pointsto_not_null with "Hsv") as %Hnn.
      rewrite (bool_decide_eq_false_2
                 (lv.(raft.raftLog.unstable').(raft.unstable.snapshot') = null) Hnn) /=.
      wp_auto.
      iApply ("HΦ" $! sv interface.nil).
      iSplitL; first reseal_raftLog.
      iPureIntro. right. split; [done|].
      destruct Hmeta as [-> _]. pose proof Hstore as (_ & _ & Hsid).
      intros Hz. rewrite Hz in Hsid. word.
    - (* [l.unstable.snapshot] is [null]: the [Storage]'s *)
      iPoseProof "Husnap" as "Hus". iEval (rewrite own_snap_None) in "Hus". iDestruct "Hus" as %Hnosnap.
      rewrite (bool_decide_eq_true_2
                 (lv.(raft.raftLog.unstable').(raft.unstable.snapshot') = null) Hnosnap) /=.
      wp_auto. rewrite Hstok /=.
      wp_apply ("HSnap" with "[$HStorage $Hesu]") as "%snap %err [HStorage %Herr]".
      iApply ("HΦ" $! snap err).
      iSplitL; last done.
      reseal_raftLog.
  Qed.

End RaftLogSnapshotProof.
