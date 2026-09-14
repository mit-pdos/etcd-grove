(** * Proof: [raft.raft__Step_MsgVote] against its spec

    Opaquely ascribed, so the proof term is sealed: callers can depend on
    nothing but the spec.  The binders arrive by [intros] rather than
    [Context] -- the lemma's type is closed, so there are no section variables
    to discharge and no [Collection W] is needed. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__Step_MsgVote.

Module StepMsgVoteProof (P : STEP_MSGVOTE_POSTULATES) : STEP_MSGVOTE.

  Lemma wp_raft__Step_MsgVote : wp_raft__Step_MsgVote_body.
  Proof.
    intros ?????? sem package_sem cfg γ r id s m.
    intros Hty Hto Hterm Hfnz.
    wp_start as "@". iNamed "Hphys". wp_auto.
    wp_apply (wp_traceReceiveMessage with "[$Hmisc]") as "Hmisc".
    (* [m.Term ≠ 0], so the first arm of the term preamble is skipped. *)
    assert (bool_decide (m.(raftpb.Message.Term') = W64 0) = false) as Hz
      by by apply bool_decide_eq_false_2.
    rewrite Hz. rewrite bool_decide_eq_false_2; last done. wp_auto.
    destruct (decide (uint.Z rv.(raft.raft.Term') < uint.Z m.(raftpb.Message.Term')))
      as [Hgt|Hle].
    - (* [m.Term > r.Term]: step down to follower first, then answer. *)
      assert (bool_decide (uint.Z rv.(raft.raft.Term') <
                           uint.Z m.(raftpb.Message.Term')) = true) as Hb
        by by apply bool_decide_eq_true_2.
      rewrite Hb. rewrite bool_decide_eq_true_2 //. wp_auto.
      rewrite Hty /MsgVote bool_decide_eq_true_2 //. wp_auto.
      (* [force] is false (not a leader transfer) and [inLease] is false (no
         check-quorum), so the lease check does not drop the message. *)
      iDestruct "Hctx" as (ctx) "[Hctx_sl %Hctx_ne]".
      wp_apply wp_string_to_bytes as "%ct_sl [ct_sl ct_cap]".
      wp_apply (wp_Equal _ _ DfracDiscarded (DfracOwn 1) ctx ("CampaignTransfer"%go)
                  with "[$Hctx_sl $ct_sl]") as "[_ ct_sl2]".
      rewrite HnoCheckQuorum. wp_auto.
      assert (bool_decide (ctx = "CampaignTransfer"%go) = false) as Hnf
        by by apply bool_decide_eq_false_2.
      rewrite Hnf. wp_auto.
      (* neither MsgPreVote nor MsgPreVoteResp, so we fall through to the
         step-down *)
      assert (bool_decide (m.(raftpb.Message.Type') = W32 17) = false) as Hpv
        by (apply bool_decide_eq_false_2; rewrite Hty /MsgVote; w32_ne).
      rewrite Hpv. rewrite bool_decide_eq_false_2; last done. wp_auto.
      assert (bool_decide (m.(raftpb.Message.Type') = W32 18) = false) as Hpvr
        by (apply bool_decide_eq_false_2; rewrite Hty /MsgVote; w32_ne).
      rewrite Hpvr. wp_auto.
      wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [Hlog_sl _]".
      wp_auto. rewrite Hlok.
      wp_apply (wp_Logger__logf with "Hlogger").
      { rewrite /log_methods. set_solver. }
      (* a [MsgVote] is not from a leader, so no leader is adopted *)
      rewrite Hty /MsgVote bool_decide_eq_false_2; last w32_ne. wp_auto.
      rewrite Hty /MsgVote bool_decide_eq_false_2; last w32_ne. wp_auto.
      rewrite Hty /MsgVote bool_decide_eq_false_2; last w32_ne. wp_auto.
      iAssert (own_raft_phys γ r id s)
        with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]" as "Hphys".
      { rewrite /own_raft_phys. iExists rv, msgs, msgsAA, lok. iFrame "∗#%". }
      wp_apply (P.wp_raft__becomeFollower with "[$Hphys]") as "Hphys".
      (* the corresponding protocol step *)
      iMod (own_raft_ghost_step_1 with "Hm Hghost") as "Hghost".
      { replace (W64 0) with
          (if from_leader (abs_msg mtype.Vote m).(msg.ty)
           then (abs_msg mtype.Vote m).(msg.from) else W64 0) by done.
        apply step_higher_term.
        - rewrite /abs_msg /= -Hterm0. exact Hgt.
        - rewrite /abs_msg /=. exact Hto. }
      iNamedSuffix "Hphys" "1".
      (* the type switch: not MsgHup / MsgStorageAppendResp / MsgStorageApplyResp,
         not MsgPreVote, but MsgVote *)
      rewrite Hty /MsgVote bool_decide_eq_false_2; last w32_ne. wp_auto.
      (* Stepping down to a strictly greater term cleared both [Vote] and
         [lead], so [canVote] holds. *)
      assert (Hne : m.(raftpb.Message.Term') ≠ s.(nstate.term)).
      { rewrite -Hterm0. intros Heq. rewrite Heq in Hgt. lia. }
      rewrite /become_follower /= decide_False // in Hvote1 Hlead1.
      rewrite Hvote1 bool_decide_eq_false_2; last congruence. wp_auto.
      rewrite Hvote1 bool_decide_eq_true_2 //. wp_auto.
      rewrite Hlead1 bool_decide_eq_true_2 //. wp_auto.
      wp_apply (wp_raftLog__lastEntryID with "[$Hlog1]") as "%lastID Hlog1".
      wp_apply (wp_raftLog__isUpToDate with "[$Hlog1]") as "%uptodate Hlog1".
      destruct uptodate.
      + (* the candidate's log is up to date: grant the vote *)
        wp_auto.
        wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
        wp_auto. rewrite Hlok1.
        wp_apply (wp_Logger__logf with "Hlogger1").
        { rewrite /log_methods. set_solver. }
        wp_apply P.wp_voteRespMsgType; first done.
        (* the protocol step: grant the vote *)
        iMod (own_raft_ghost_step_1_1 with "Hm Hghost") as "[Hghost #Hgrant]".
        { apply step_grant_vote; [done|exact Hto|done|].
          rewrite /can_vote /become_follower /=. right.
          split; [by rewrite decide_False|done]. }
        iEval (rewrite /abs_msg /become_follower /=) in "Hgrant".
        iAssert (own_raft_phys γ r id (become_follower s m.(raftpb.Message.Term') (W64 0)))
          with "[Hr1 Htrk1 Hlog1 Hmsgs1 Hmsgs_cap1 HmsgsAA1 HmsgsAA_cap1 Hmisc1]"
          as "Hphys".
        { rewrite /own_raft_phys. iExists rv0, msgs0, msgsAA0, lok0.
          rewrite /become_follower /= decide_False //. iFrame "∗#%". }
        (* TODO: the remaining steps are [send] of the granted vote and the
           [r.Vote := m.From] update; see notes/raft-election-refinement.md *)
        admit.
      + admit.
    - admit.
  Admitted.

End StepMsgVoteProof.
