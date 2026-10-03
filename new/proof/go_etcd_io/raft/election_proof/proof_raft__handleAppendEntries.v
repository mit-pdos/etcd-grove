Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__handleAppendEntries.

Module RaftHandleAppendEntriesProof (P : RAFT__HANDLEAPPENDENTRIES_POSTULATES) : RAFT__HANDLEAPPENDENTRIES.
Import P.

  (** The three exits of [handle_app_result], in the body's order.

      - [a.prev.index < committed]: [committed] is read twice through the
        log's struct ([own_raftLog_struct]), once for the test and once
        for the reply.
      - [maybeAppend]: the log is taken out at its state and put back at
        whatever [maybeAppend] leaves ([own_raft_phys_log_at]); on [ok]
        that is the new [ls'], on [!ok] its spec says [ls' = ls].
      - the reject path: the [Debugf]'s arguments call [term(m.Index)] and
        hand its error to [zeroTermOnOutOfBounds], whose premise is
        exactly [term]'s last conjunct; then [min(m.Index, lastIndex())],
        [findConflictByTerm], and the rejecting reply.

      Every [send] is [send_ok]'s [MsgAppResp] clause (d) with no
      entries. *)
  Lemma wp_raft__handleAppendEntries : wp_raft__handleAppendEntries_body.
  Proof.
    intros_ambient.
    intros cfg r id s m ents Hwf Hnw Hnorm Hconf.
    wp_start as "(Hphys & #Hents & Hcap)". wp_auto.
    wp_apply (wp_logSliceFromMsgApp with "[$m]") as "m".
    (* the stale test reads [r.raftLog.committed] *)
    wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
    iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hlogback]".
    iDestruct (own_raftLog_struct with "Hlog") as (lv) "(Hl & %Hlv & Hlb)".
    wp_auto.
    iDestruct ("Hlb" with "Hl") as "Hlog".
    iDestruct ("Hlogback" with "Hlog") as "Hphys".
    destruct Hlv as [Hcm _]. rewrite Hcm.
    destruct (decide (uint.Z m.(raftpb.Message.Index')
                      < uint.Z s.(nstate.logst).(logstate.committed))%Z) as [Hst|Hst].
    - (* stale: acknowledge [committed] *)
      rewrite bool_decide_eq_true_2 //. wp_auto.
      wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
      iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hlogback]".
      iDestruct (own_raftLog_struct with "Hlog") as (lv2) "(Hl & %Hlv2 & Hlb)".
      wp_auto.
      iDestruct ("Hlb" with "Hl") as "Hlog".
      iDestruct ("Hlogback" with "Hlog") as "Hphys".
      destruct Hlv2 as [Hcm2 _]. rewrite Hcm2.
      wp_apply (wp_raft__send _ _ _ _ _ []
                  [app_resp id s m.(raftpb.Message.From') false
                     s.(nstate.logst).(logstate.committed) (W64 0) (W64 0)]
                  with "[$Hphys]").
      { done. }
      { right; right; right; left. split_and!; [done|done|reflexivity]. }
      { iSplitR; [iApply own_slice_nil | iApply send_no_snap; simpl; w32_ne]. }
      iIntros "Hphys". wp_auto.
      iApply "HΦ". iFrame "Hphys". iPureIntro. left. split; [lia|done].
    - (* [maybeAppend] *)
      rewrite bool_decide_eq_false_2; last lia. wp_auto.
      wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
      iDestruct (own_raft_phys_log_at with "Hphys") as "[Hlog Hlogback]".
      wp_apply (wp_raftLog__maybeAppend _ s.(nstate.logst)
                  (raft.logSlice.mk m.(raftpb.Message.Term')
                     (raft.entryID.mk m.(raftpb.Message.LogTerm') m.(raftpb.Message.Index'))
                     m.(raftpb.Message.Entries'))
                  ents m.(raftpb.Message.Commit') Hwf Hnw Hnorm
                  with "[$Hlog $Hents $Hcap]").
      { intros Hm. apply Hconf; [lia|exact Hm]. }
      iIntros (lastnewi ok ls') "[Hlog %Hma]".
      iDestruct ("Hlogback" with "Hlog") as "Hphys".
      destruct (plog_maybe_append _ _ _ _) as [[lni es']|] eqn:Hpm.
      + (* accepted *)
        destruct Hma as (-> & -> & Hprev & Hes & Happ & Hcm').
        wp_auto.
        wp_apply (wp_raft__send _ _ _ _ _ []
                    [app_resp id s m.(raftpb.Message.From') false lni (W64 0) (W64 0)]
                    with "[$Hphys]").
        { done. }
        { right; right; right; left. split_and!; [done|done|reflexivity]. }
        { iSplitR; [iApply own_slice_nil | iApply send_no_snap; simpl; w32_ne]. }
        iIntros "Hphys". wp_auto.
        iApply "HΦ". iFrame "Hphys". iPureIntro. right; left.
        split; [lia|]. exists lni, es', ls'. split_and!; done.
      + (* rejected: [a.prev] does not match *)
        destruct Hma as (-> & -> & ->).
        iDestruct (own_raft_phys_eq _ _ _ _ s with "Hphys") as "Hphys".
        { by destruct s. }
        assert (Hnm : ¬ plog_matches s.(nstate.logst).(logstate.prev)
                        (s.(nstate.logst).(logstate.sents) ++ s.(nstate.logst).(logstate.uents))
                        (raft.entryID.mk m.(raftpb.Message.LogTerm') m.(raftpb.Message.Index'))).
        { rewrite /plog_maybe_append in Hpm. case_decide; done. }
        wp_auto.
        wp_apply (wp_raft_load_id with "Hphys") as "Hphys".
        wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
        iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hlogback]".
        wp_apply (wp_raftLog__term with "[$Hlog]") as "%t %err (Hlog & _ & _ & #Herr)".
        iDestruct ("Hlogback" with "Hlog") as "Hphys".
        wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
        wp_apply (wp_raftLog__zeroTermOnOutOfBounds with "[$Herr]") as "%t' _".
        wp_raft_log.
        (* [hintIndex := min(m.Index, lastIndex())] *)
        wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
        iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hlogback]".
        wp_apply (wp_raftLog__lastIndex with "[$Hlog]") as "%li [Hlog _]".
        iDestruct ("Hlogback" with "Hlog") as "Hphys".
        wp_apply wp_min2_uint64.
        wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
        iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hlogback]".
        wp_apply (wp_raftLog__findConflictByTerm with "[$Hlog]") as "%hint %hintterm [Hlog _]".
        iDestruct ("Hlogback" with "Hlog") as "Hphys".
        wp_apply (wp_raft__send _ _ _ _ _ []
                    [app_resp id s m.(raftpb.Message.From') true m.(raftpb.Message.Index')
                       hintterm hint]
                    with "[$Hphys]").
        { done. }
        { right; right; right; left. split_and!; [done|done|reflexivity]. }
        { iSplitR; [iApply own_slice_nil | iApply send_no_snap; simpl; w32_ne]. }
        iIntros "Hphys". wp_auto.
        iApply "HΦ". iFrame "Hphys". iPureIntro. right; right.
        split; [lia|]. split; [exact Hnm|]. by exists hint, hintterm.
  Qed.

End RaftHandleAppendEntriesProof.
