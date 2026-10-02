Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__handleHeartbeat.

Module RaftHandleHeartbeatProof (P : RAFT__HANDLEHEARTBEAT_POSTULATES)
  : RAFT__HANDLEHEARTBEAT.
Import P.

  (** [commitTo] on the log taken out with [own_raft_phys_log_at] and put
      back at the new [committed]; then [send] of the literal under
      [send_ok]'s clause (b).  The literal's [Entries] is [slice.nil], so
      [ents = []] ([own_slice_nil]). *)
  Lemma wp_raft__handleHeartbeat : wp_raft__handleHeartbeat_body.
  Proof.
    intros_ambient.
    intros cfg r id s m Hcommit Hfrom.
    wp_start as "Hphys". iNamed "Hphys".
    wp_auto.
    wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
    iDestruct (own_raft_phys_log_at with "Hphys") as "[Hlog Hlogback]".
    wp_apply (wp_raftLog__commitTo _ _ _ Hcommit with "[$Hlog]") as "Hlog".
    iDestruct ("Hlogback" with "Hlog") as "Hphys".
    try wp_auto.
    wp_apply (wp_raft__send _ _ _ _ _ [] with "[$Hphys]").
    { done. }
    { right; left. exists mtype.HeartbeatResp. split_and!;
        [ by right; right; right | reflexivity | done | exact Hfrom | reflexivity ]. }
    { iApply own_slice_nil. }
    iIntros "Hphys". wp_auto.
    by iApply "HΦ".
  Qed.

End RaftHandleHeartbeatProof.
