Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__sendHeartbeat.

Module RaftSendHeartbeatProof (P : RAFT__SENDHEARTBEAT_POSTULATES)
  : RAFT__SENDHEARTBEAT.
Import P.

  (** The lookup hits ([to ∈ cfg]; same steps as [maybeSendAppend]).
      [pr.Match] is read with [pr] borrowed by its key
      ([own_raft_phys_pr]), [r.raftLog.committed] through the log's record
      ([own_raftLog_struct]), [min] by [wp_min2_uint64].  [send] changes
      only the outbox, so [pr] is still at [p] for [SentCommit],
      which writes only [sentCommit] ([prvals_match_insert_same]). *)
  Lemma wp_raft__sendHeartbeat : wp_raft__sendHeartbeat_body.
  Proof.
    intros_ambient.
    intros cfg r id s to ctx Hto Hcfg.
    wp_start_folded as "Hphys".
    iNamed "Hphys".
    iDestruct (own_raft_phys_tracker_same with "Hphys") as (tv) "(Htrkf & Htrk & Hback)".
    iDestruct (own_tracker_progress_map with "Htrk") as "(#Hprs & %Hdom & Htrk)".
    iDestruct (own_tracker_prvals_dom with "Htrk") as "[%Hpdom Htrk]".
    assert (is_Some (s.(nstate.progress) !! to)) as [pr Hlk].
    { apply elem_of_dom. rewrite Hdom //. }
    assert (is_Some (s.(nstate.prvals) !! to)) as [p Hpvs].
    { apply elem_of_dom. rewrite Hpdom elem_of_dom. by eexists. }
    wp_start_unfold.
    wp_auto.
    iDestruct ("Hback" with "Htrkf Htrk") as "Hphys".
    wp_apply (wp_map_lookup1 with "Hprs") as "_".
    rewrite Hlk /=.
    (* [pr.Match], then [r.raftLog.committed] *)
    iDestruct (own_raft_phys_pr with "Hphys [//] [//]") as "[Hpa Hpback]".
    iNamed "Hpa".
    pose proof Habs as Habs0.
    apply progress_abs_Some in Habs0 as (_ & _ & Hm & _).
    wp_auto. rewrite Hm.
    iDestruct ("Hpback" with "[Hpv Hinfl]") as "Hphys".
    { iExists _. iFrame "∗%". }
    wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
    iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hlogback]".
    iDestruct (own_raftLog_struct with "Hlog") as (lv) "(Hl & %Hlv & Hlb)".
    wp_auto.
    iDestruct ("Hlb" with "Hl") as "Hlog".
    iDestruct ("Hlogback" with "Hlog") as "Hphys".
    wp_apply wp_min2_uint64.
    try wp_auto.
    wp_apply (wp_raft__send _ _ _ _ _ [] with "[$Hphys]").
    { done. }
    { right; left. exists mtype.Heartbeat. split_and!;
        [ by right; left | reflexivity | done | exact Hto | reflexivity ]. }
    { iSplitR; [iApply own_slice_nil | iApply send_no_snap; simpl; w32_ne]. }
    iIntros "Hphys". wp_auto.
    iDestruct (own_raft_phys_pr_upd with "Hphys [//] [//]") as "[Hpa Hpback]".
    wp_apply (wp_Progress__SentCommit with "[$Hpa]") as "Hpa".
    iDestruct ("Hpback" with "Hpa") as "Hphys".
    try wp_auto.
    iApply "HΦ". iFrame "Hphys".
    destruct Hlv as [Hlv _].
    iPureIntro. cbn [raftpb.Message.Commit']. split_and!.
    - rewrite -Hlv. pose proof (w64_min_spec p.(progress.matched) lv.(raft.raftLog.committed')). lia.
    - rewrite /prvals_match lookup_fmap Hpvs /=.
      pose proof (w64_min_spec p.(progress.matched) lv.(raft.raftLog.committed')). lia.
    - apply (prvals_match_insert_same _ _ p); done.
  Qed.

End RaftSendHeartbeatProof.
