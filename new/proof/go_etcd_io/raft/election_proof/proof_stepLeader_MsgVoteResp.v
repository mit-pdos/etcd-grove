Require Export New.proof.go_etcd_io.raft.election_proof.postulates_stepLeader_MsgVoteResp.

Module StepLeaderProof (P : STEPLEADER_POSTULATES) : STEPLEADER.

  (** Walk both type switches and fall off the end of each.

      The structure, and why each piece is there:

      - The first switch ([MsgBeat], [MsgCheckQuorum], [MsgProp],
        [MsgReadIndex], [MsgForgetLeader]) needs exactly one manual
        [bool_decide]: rewriting [m.(Message.Type')] to the literal [W32 6]
        substitutes into the not-yet-stepped comparisons too, so [wp_auto]
        computes the remaining four.

      - Between the switches the code reads [r.trk.Progress] and looks up
        [m.From].  That is the only place the struct is touched (contrast
        [stepFollower], which never touches it): [own_raft_phys_tracker]
        hands out the tracker field, through which [wp_auto] reads
        [Progress], and [own_tracker_progress_map] the map's points-to.
        [m.From] is *not* known to be a voter -- the message could be from
        anyone -- so [wp_tracker_progress_lookup] (which has an [i ∈ cfg]
        side condition) does not apply; the generic [wp_map_lookup1] does.

      - The [pr == nil] test is decided by [case_bool_decide] rather than
        being resolved: we deliberately do *not* prove which way it goes.
        On [nil] the code logs with [Debugf] and returns; otherwise it enters
        the second switch, which a [MsgVoteResp] also falls through.  Both
        arms end at the same trailing [return nil] with the struct untouched,
        so the spec holds without knowing whether [m.From] is a voter.

      - No [Panicf] is reachable.  [stepLeader]'s only [Panicf] is in the
        [MsgProp] arm of the first switch ("%x stepped empty MsgProp"), which
        a [MsgVoteResp] does not enter; [Debugf] is in [log_methods]. *)
  Lemma wp_stepLeader_MsgVoteResp : wp_stepLeader_MsgVoteResp_body.
  Proof.
    intros_ambient.
    intros cfg r id s m.
    intros Hty Hlent.
    wp_start as "Hphys".
    wp_auto.
    (* first switch *)
    rewrite Hty /MsgVoteResp.
    rewrite bool_decide_eq_false_2; last w32_ne.
    wp_auto.
    (* pr := r.trk.Progress[m.From]: read the field, keep the map's
       points-to (persistent) and give the tracker back unchanged *)
    iDestruct (own_raft_phys_tracker with "Hphys")
      as (tv) "(Htrkf & Htrk & Hback)"; first exact Hlent.
    iDestruct (own_tracker_progress_map with "Htrk") as "(#Hprs & _ & Htrk)".
    wp_auto.
    iDestruct ("Hback" with "Htrkf Htrk") as "Hphys".
    iDestruct (own_raft_phys_eq _ _ _ _ s with "Hphys") as "Hphys".
    { by destruct s. }
    wp_apply (wp_map_lookup1 with "Hprs") as "_".
    case_bool_decide as Hnil.
    - (* no progress for the sender: log and return nil *)
      wp_auto.
      (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_raft_log).
      iApply ("HΦ" $! interface.nil).
      iFrame "Hphys". done.
    - (* the sender has a [Progress]: the second switch ignores us *)
      wp_auto.
      rewrite Hty /MsgVoteResp.
      rewrite bool_decide_eq_false_2; last w32_ne.
      wp_auto.
      iApply ("HΦ" $! interface.nil).
      iFrame "Hphys". done.
  Qed.

End StepLeaderProof.
