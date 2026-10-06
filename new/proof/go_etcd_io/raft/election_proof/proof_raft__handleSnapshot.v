Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__handleSnapshot.

Module RaftHandleSnapshotProof (P : RAFT__HANDLESNAPSHOT_POSTULATES) : RAFT__HANDLESNAPSHOT.
Import P.

  (** [m.Snapshot] points to [sv], so the copy [s = *m.Snapshot] is taken
      and the [nil] arm is dead.  Then [restore]'s three exits: on [true]
      (a restore) the reply carries [lastIndex()], the snapshot's index; on
      [false] it carries [committed], the old one (obsolete) or the
      snapshot's (fast-forward).  Each [send] is [send_ok]'s [MsgAppResp]
      clause with no entries, as in [handleAppendEntries]. *)
  Lemma wp_raft__handleSnapshot : wp_raft__handleSnapshot_body.
  Proof.
    intros_ambient.
    intros cfg r id s m sv voters Hrole Hvotes Hin Hscope.
    wp_start as "H". iNamed "H". wp_auto.
    iDestruct (typed_pointsto_not_null with "Hsv") as %Hnn.
    rewrite (bool_decide_eq_false_2 (m.(raftpb.Message.Snapshot') = null) Hnn) /=.
    wp_auto.
    wp_apply (P.wp_raft__restore _ _ _ _ sv voters Hrole Hvotes Hin Hscope
                with "[$Hphys $Hvoters]") as "%b %s1 [Hphys %Hres]".
    destruct Hres as [(Hst & -> & ->)|[(Hlt & Hm & -> & ->)|(Hlt & Hnm & -> & prs & pvs & ->)]].
    - (* obsolete: acknowledge the commit index *)
      wp_auto.
      wp_apply (wp_raft_load_id with "Hphys") as "Hphys".
      wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
      iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hlogback]".
      iDestruct (own_raftLog_struct with "Hlog") as (lv) "(Hl & %Hlv & Hlb)".
      wp_auto.
      iDestruct ("Hlb" with "Hl") as "Hlog".
      iDestruct ("Hlogback" with "Hlog") as "Hphys".
      wp_raft_log.
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
      { by left. }
      { right; right; right; left. split_and!; [done|done|reflexivity]. }
      { iSplitR; [iApply own_slice_nil | iApply send_no_snap; simpl; w32_ne]. }
      iIntros "Hphys". wp_auto.
      iApply "HΦ". iFrame "Hphys". iPureIntro. left. split; [exact Hst|done].
    - (* fast-forward: acknowledge the new commit index, the snapshot's *)
      wp_auto.
      wp_apply (wp_raft_load_id with "Hphys") as "Hphys".
      wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
      iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hlogback]".
      iDestruct (own_raftLog_struct with "Hlog") as (lv) "(Hl & %Hlv & Hlb)".
      wp_auto.
      iDestruct ("Hlb" with "Hl") as "Hlog".
      iDestruct ("Hlogback" with "Hlog") as "Hphys".
      wp_raft_log.
      wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
      iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hlogback]".
      iDestruct (own_raftLog_struct with "Hlog") as (lv2) "(Hl & %Hlv2 & Hlb)".
      wp_auto.
      iDestruct ("Hlb" with "Hl") as "Hlog".
      iDestruct ("Hlogback" with "Hlog") as "Hphys".
      destruct Hlv2 as [Hcm2 _]. rewrite Hcm2.
      wp_apply (wp_raft__send _ _ _ _ _ []
                  [app_resp id s m.(raftpb.Message.From') false
                     (snap_id sv).(raft.entryID.index') (W64 0) (W64 0)]
                  with "[$Hphys]").
      { by left. }
      { right; right; right; left. split_and!; [done|done|reflexivity]. }
      { iSplitR; [iApply own_slice_nil | iApply send_no_snap; simpl; w32_ne]. }
      iIntros "Hphys". wp_auto.
      iApply "HΦ". iFrame "Hphys". iPureIntro. right; left. split_and!; [exact Hlt|exact Hm|done].
    - (* a restore: acknowledge the new last index, the snapshot's *)
      wp_auto.
      wp_apply (wp_raft_load_id with "Hphys") as "Hphys".
      wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
      iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hlogback]".
      iDestruct (own_raftLog_struct with "Hlog") as (lv) "(Hl & %Hlv & Hlb)".
      wp_auto.
      iDestruct ("Hlb" with "Hl") as "Hlog".
      iDestruct ("Hlogback" with "Hlog") as "Hphys".
      wp_raft_log.
      wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
      iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hlogback]".
      wp_apply (wp_raftLog__lastIndex with "[$Hlog]") as "%li [Hlog %Hli]".
      iDestruct ("Hlogback" with "Hlog") as "Hphys".
      assert (li = (snap_id sv).(raft.entryID.index')) as ->.
      { apply word.unsigned_inj. rewrite Hli /log_restore /=. lia. }
      wp_apply (wp_raft__send _ _ _ _ _ []
                  [app_resp id s m.(raftpb.Message.From') false
                     (snap_id sv).(raft.entryID.index') (W64 0) (W64 0)]
                  with "[$Hphys]").
      { by left. }
      { right; right; right; left. split_and!; [done|done|reflexivity]. }
      { iSplitR; [iApply own_slice_nil | iApply send_no_snap; simpl; w32_ne]. }
      iIntros "Hphys". wp_auto.
      iApply "HΦ". iFrame "Hphys". iPureIntro. right; right.
      split_and!; [exact Hlt|exact Hnm|]. by exists prs, pvs.
  Qed.

End RaftHandleSnapshotProof.
