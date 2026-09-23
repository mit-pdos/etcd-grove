(** One term case of [Step]'s [MsgVote] branch, in its own file so that it
    checks in parallel with the other -- see [proof_raft__Step_MsgVote.v],
    which combines the two, and [notes/decisions.md] (2026-09-17; 2026-09-18
    for why this directory exists).  Proof
    structure, not specification: no [Module Type], no [Parameter]; only
    [proof_raft__Step_MsgVote.v] may [Require] this file. *)
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__Step.

Module StepMsgVoteGt (P : STEP_POSTULATES).
Import P.

Section branches.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).

Implicit Type γ : raft_election_names.
Implicit Type s : nstate.t.

  (** [∀ m', m' ∈ recv → m' = a] for the concrete [recv] lists this file
      produces ([[]], [[a]], [[a] ++ [a]]).  Not [set_solver]: on these goals
      it ran for 150s and more (its [setoid_subst] / [naive_solver eauto] over
      this context), where rewriting the membership away is ~1s. *)
  Local Ltac recv_elem :=
    intros ? Hin;
    rewrite ?elem_of_app ?list_elem_of_singleton ?elem_of_nil in Hin;
    naive_solver.

  (** [MsgVote] with [m.Term > r.Term]: step down to follower first, then
      grant or decline in the new term. *)
  Lemma wp_Step_MsgVote_gt r id s (m : raftpb.Message.t) :
    m.(raftpb.Message.Type') = MsgVote →
    m.(raftpb.Message.To') = id →
    m.(raftpb.Message.Term') ≠ W64 0 →
    (* [send] stamps the sender's id into [From], and node ids are nonzero *)
    m.(raftpb.Message.From') ≠ W64 0 →
    (* this file: the incoming term is strictly higher, so [Step] steps down first *)
    uint.Z s.(nstate.term) < uint.Z m.(raftpb.Message.Term') →
    (* [r.step] matches the role and nothing is on loan *)
    nstate_wf s →
    {{{ is_pkg_init raft ∗
        "Hphys" ∷ own_raft_phys cfg r id s ∗
        (* the message's [Context] is readable and is not the leader-transfer
           marker: leader transfer is out of scope *)
        "#Hctx" ∷ (∃ ctx, m.(raftpb.Message.Context') ↦*□ ctx ∗
                          ⌜ ctx ≠ campaignTransfer ⌝)
    }}}
      r @! (go.PointerType raft.raft) @! "Step" #m
    {{{ (err : error.t) s', RET #err;
        "Hphys" ∷ own_raft_phys cfg r id s' ∗
        "%Hwf'" ∷ ⌜ nstate_wf s' ⌝ ∗
        (* [recv] is whatever this branch consumed -- nothing, or the incoming
           message once or twice.  Naming its elements rather than the list
           lets [wp_raft__Step] discharge the [is_message] side of
           [own_raft_ghost_step] from the single fact it holds about [m]. *)
        "%Hrefines" ∷ ⌜ ∃ recv,
            (∀ m', m' ∈ recv → m' = abs_msg mtype.Vote m) ∧
            step cfg id (to_pstate s) recv (to_pstate s') ⌝ ∗
        "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.
  Proof.
    intros Hty Hto Hterm Hfnz Hgt0 Hwf.
    pose proof Hwf as [Hsfw Hlent].
    wp_start_folded as "@". iNamed "Hphys". wp_start_unfold. wp_auto.
    assert (Hgt : uint.Z rv.(raft.raft.Term') < uint.Z m.(raftpb.Message.Term'))
      by (rewrite Hterm0; exact Hgt0).
    wp_apply wp_traceReceiveMessage. try wp_auto.
    (* [m.Term ≠ 0], so the first arm of the term preamble is skipped. *)
    assert (bool_decide (m.(raftpb.Message.Term') = W64 0) = false) as Hz
    by by apply bool_decide_eq_false_2.
    rewrite Hz. rewrite bool_decide_eq_false_2; last done. wp_auto.
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
    { solve_log_method. }
    (* a [MsgVote] is not from a leader, so no leader is adopted *)
    rewrite Hty /MsgVote bool_decide_eq_false_2; last w32_ne. wp_auto.
    rewrite Hty /MsgVote bool_decide_eq_false_2; last w32_ne. wp_auto.
    rewrite Hty /MsgVote bool_decide_eq_false_2; last w32_ne. wp_auto.
    iAssert (own_raft_phys cfg r id s)
      with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]" as "Hphys".
    { iApply (own_raft_phys_intro with
          "Hr Hlogger Hprs Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc"); done. }
    wp_apply (P.wp_raft__becomeFollower _ _ _ _ _ _ Hlent with "[$Hphys]")
      as "Hphys".
    (* the corresponding protocol step, recorded as a pure fact rather than
       taken on the ghost state: this lemma is ghost-free. *)
    assert (step cfg id (to_pstate s) [abs_msg mtype.Vote m]
              (to_pstate (become_follower s m.(raftpb.Message.Term') (W64 0)))) as Hstepdown.
    { rewrite to_pstate_become_follower.
      replace (W64 0) with
        (if from_leader (abs_msg mtype.Vote m).(msg.ty)
         then (abs_msg mtype.Vote m).(msg.from) else W64 0) by done.
      replace m.(raftpb.Message.Term') with (abs_msg mtype.Vote m).(msg.term)
        by done.
      apply step_higher_term.
      - rewrite /abs_msg /= -Hterm0. exact Hgt.
      - rewrite /abs_msg /=. exact Hto. }
    wp_hidden (iNamedSuffix "Hphys" "1").
    (* the type switch: not MsgHup / MsgStorageAppendResp / MsgStorageApplyResp,
       not MsgPreVote, but MsgVote *)
    rewrite Hty /MsgVote bool_decide_eq_false_2; last w32_ne. wp_auto.
    (* Stepping down to a strictly greater term cleared both [Vote] and
       [lead], so [canVote] holds. *)
    assert (Hne : m.(raftpb.Message.Term') ≠ s.(nstate.term)).
    { rewrite -Hterm0. intros Heq. rewrite Heq in Hgt. lia. }
    rewrite /become_follower /reset_to /= decide_False // in Hvote1 Hlead1.
    rewrite Hvote1 bool_decide_eq_false_2; last congruence. wp_auto.
    rewrite Hvote1 bool_decide_eq_true_2 //. wp_auto.
    rewrite Hlead1 bool_decide_eq_true_2 //. wp_auto.
    iDestruct (own_raftLog_unless_open _ _ Hlent with "Hlog1") as "Hlog1".
    wp_apply (wp_raftLog__lastEntryID with "[$Hlog1]") as "%lastID Hlog1".
    wp_apply (wp_raftLog__isUpToDate with "[$Hlog1]") as "%uptodate Hlog1".
    iDestruct (own_raftLog_unless_close _ _ Hlent with "Hlog1") as "Hlog1".
    destruct uptodate.
    + (* the candidate's log is up to date: grant the vote *)
      wp_auto.
      wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
      wp_auto. rewrite Hlok1.
      wp_apply (wp_Logger__logf with "Hlogger1").
      { solve_log_method. }
      wp_apply P.wp_voteRespMsgType; first done.
      (* the protocol step: grant the vote.  The [VoteResp] it sends is no
         longer a separate output -- it is the growth of the outbox, which the
         [send] below has to match. *)
      assert (step cfg id (to_pstate (become_follower s m.(raftpb.Message.Term') (W64 0)))
                [abs_msg mtype.Vote m]
                (to_pstate
                  (send_msgs ((become_follower s m.(raftpb.Message.Term') (W64 0))
                                <| nstate.vote := m.(raftpb.Message.From') |>)
                     [msg.mk mtype.VoteResp id m.(raftpb.Message.From')
                        m.(raftpb.Message.Term') false]))) as Hgrant.
      { rewrite to_pstate_send_msgs to_pstate_vote to_pstate_become_follower.
        apply step_grant_vote; [done|exact Hto|done|done|].
        rewrite /pcan_vote /pbecome_follower /=. right.
        split; [by rewrite decide_False|done]. }
      iAssert (own_raft_phys cfg r id (become_follower s m.(raftpb.Message.Term') (W64 0)))
        with "[Hr1 Htrk1 Hlog1 Hmsgs1 Hmsgs_cap1 HmsgsAA1 HmsgsAA_cap1 Hmisc1]"
        as "Hphys".
      { iApply (own_raft_phys_intro with
          "Hr1 Hlogger1 Hprs1 Htrk1 Hlog1 Hmsgs1 Hmsgs_cap1 HmsgsAA1 HmsgsAA_cap1 Hmisc1");
        unfold become_follower, reset_to; simpl; try (rewrite decide_False; [|exact Hne]); done. }
      (* [send] the granted vote response, then record the vote. *)
      wp_apply (P.wp_raft__send with "[$Hphys]") as "Hphys".
      { done. }
      { left; exists mtype.VoteResp; split_and!;
          [by right | apply mtype_of_MsgVoteResp | done | w32_ne | done]. }
      wp_hidden (iNamedSuffix "Hphys" "2").
      (* [m.Type = MsgVote], so the vote is recorded: [r.Vote := m.From]. *)
      rewrite Hty /MsgVote bool_decide_eq_true_2 //. wp_auto.
      iApply ("HΦ" $! interface.nil
        (send_msgs ((become_follower s m.(raftpb.Message.Term') (W64 0))
                      <| nstate.vote := m.(raftpb.Message.From') |>)
           [msg.mk mtype.VoteResp id m.(raftpb.Message.From')
              m.(raftpb.Message.Term') false])).
      iSplitL "Hr2 Htrk2 Hlog2 Hmsgs2 Hmsgs_cap2 HmsgsAA2 HmsgsAA_cap2 Hmisc2".
      { (* the state is given explicitly: [send]'s postcondition states the
           outbox with [send]'s form of the message *)
        iApply (own_raft_phys_intro _ _ _
          (send_msgs ((become_follower s m.(raftpb.Message.Term') (W64 0))
                        <| nstate.vote := m.(raftpb.Message.From') |>)
             [msg.mk mtype.VoteResp id m.(raftpb.Message.From')
                m.(raftpb.Message.Term') false]) with
          "Hr2 Hlogger2 Hprs2 Htrk2 Hlog2 Hmsgs2 Hmsgs_cap2 HmsgsAA2 HmsgsAA_cap2 Hmisc2");
          done. }
      iPureIntro. split; first exact (nstate_wf_become_follower _ _ _ Hlent).
      split; last done.
      eexists ([abs_msg mtype.Vote m] ++ [abs_msg mtype.Vote m]).
      split.
      { recv_elem. }
      eapply step_trans; [exact Hstepdown|exact Hgrant].
    + (* the candidate's log is behind: decline, without recording a vote *)
      wp_auto.
      wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
      wp_auto. rewrite Hlok1.
      wp_apply (wp_Logger__logf with "Hlogger1").
      { solve_log_method. }
      wp_apply P.wp_voteRespMsgType; first done.
      (* [r.Term] is [m.Term] after the step-down, so the rejection carries
         the state's term -- which is what [step_reject_vote] sends. *)
      assert (Hrt : rv0.(raft.raft.Term') = m.(raftpb.Message.Term'))
        by by rewrite Hterm1.
      rewrite Hrt.
      iAssert (own_raft_phys cfg r id
                 (become_follower s m.(raftpb.Message.Term') (W64 0)))
        with "[Hr1 Htrk1 Hlog1 Hmsgs1 Hmsgs_cap1 HmsgsAA1 HmsgsAA_cap1 Hmisc1]"
        as "Hphys".
      { iApply (own_raft_phys_intro with
          "Hr1 Hlogger1 Hprs1 Htrk1 Hlog1 Hmsgs1 Hmsgs_cap1 HmsgsAA1 HmsgsAA_cap1 Hmisc1");
        unfold become_follower, reset_to; simpl; try (rewrite decide_False; [|exact Hne]); done. }
      wp_apply (P.wp_raft__send with "[$Hphys]") as "Hphys".
      { done. }
      { left; exists mtype.VoteResp; split_and!;
          [by right | apply mtype_of_MsgVoteResp | done | w32_ne | done]. }
      iApply ("HΦ" $! interface.nil _). iFrame "Hphys".
      iPureIntro. split; first exact (nstate_wf_become_follower _ _ _ Hlent).
      split; last done.
      eexists ([abs_msg mtype.Vote m] ++ [abs_msg mtype.Vote m]).
      split.
      { recv_elem. }
      rewrite to_pstate_send_msgs to_pstate_become_follower.
      apply (step_stepdown_then_reject cfg id (to_pstate s) (abs_msg mtype.Vote m));
        [done|exact Hto|rewrite /abs_msg /= -Hterm0; exact Hgt].
  Qed.

End branches.

End StepMsgVoteGt.
