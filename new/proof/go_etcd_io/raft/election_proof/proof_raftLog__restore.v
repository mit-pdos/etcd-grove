Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raftLog__restore.

Module RaftLogRestoreProof (P : RAFTLOG__RESTORE_POSTULATES) : RAFTLOG__RESTORE.
Import P.

  (** Straight-line: the [Infof] through [l.logger], the [committed] store,
      and [unstable.restore] on the [unstable] field (split out with a wand
      taking any new value, [raftLog_split_unstable]).  The log is re-sealed
      at [log_restore]: the [Storage] and its contents carried over
      unchanged, now shadowed ([log_store_ok]'s [Some] case). *)
  Lemma wp_raftLog__restore : wp_raftLog__restore_body.
  Proof.
    intros_ambient.
    intros l ls sv voters Hcmlt Hlt.
    destruct ls as [prev sents uents lcm lap snap]; logstate_simpl.
    wp_start as "H". iNamed "H".
    iNamed "Hlog".
    iEval (rewrite /own_raftLog_core /=) in "Hcore". iNamed "Hcore".
    iPoseProof "Hl_logger" as "Hlgv". iEval (rewrite /is_Logger_val) in "Hlgv".
    iDestruct "Hlgv" as (lg Hlg) "#Hlgr".
    wp_auto.
    wp_apply wp_slice_literal.
    try (iSplitR; [ done | ]); try iIntros "% [? _]"; try wp_auto.
    rewrite Hlg. try wp_auto.
    wp_apply (wp_Logger__logf with "Hlgr"); first solve_log_method.
    try iIntros "_". try wp_auto.
    iDestruct (raftLog_split_unstable with "Hl") as "[Huf Hlback]".
    wp_apply (wp_unstable__restore _ _ _ _ voters with "[Huf Huents Huents_cap]")
      as "%uv' (Hun & #Hsn & %Huv')".
    { rewrite /own_unstable. iFrame "Huf Huents Huents_cap Hvoters". }
    destruct Huv' as [Hoff' Hlg'].
    iNamed "Hun".
    iDestruct ("Hlback" with "Hu") as "Hl".
    try wp_auto.
    iApply "HΦ".
    iEval (rewrite -Hlg') in "Hu_logger".
    iEval (rewrite -Hlg) in "Hl_logger".
    rewrite /log_restore.
    pose proof (f_equal uint.Z Hcm) as HcmZ. pose proof (f_equal uint.Z Hap) as HapZ.
    simpl in HcmZ, HapZ. rewrite /snap_id /= in Hcmlt Hlt.
    iApply (own_raftLog_intro with
             "Hl HisStorage HStorage Hsn Hents Hents_cap Hl_logger Hu_logger");
      try done.
    all: try unfold snap_id; simpl.
    - lia.
    - split; [done|split; [done|split; word]].
    - rewrite Hoff'. word.
    - split; lia.
    - lia.
  Qed.

End RaftLogRestoreProof.
