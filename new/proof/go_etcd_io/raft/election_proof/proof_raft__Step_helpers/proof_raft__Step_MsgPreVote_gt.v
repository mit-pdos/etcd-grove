(** One term case of [Step]'s [MsgPreVote] branch (2026-10-04): the
    incoming term is higher.  In its own file so that it checks in parallel
    with the others; [proof_raft__Step_MsgPreVote.v] combines them.  Proof
    structure, not specification: no [Module Type], no [Parameter]; only
    files in this directory may [Require] it. *)
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_prevote_lemmas.

Module StepMsgPreVoteGt (P : STEP_POSTULATES).
Import P.

Section branches.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).

Implicit Type s : nstate.t.

  (** One step of [canVote]'s evaluation, whatever its outcome: a field
      load, or a comparison decided by case analysis. *)
  Local Ltac cv_step :=
    first
      [ progress wp_auto
      | wp_apply (wp_raft_load_Vote with "Hphys") as "Hphys"
      | wp_apply (wp_raft_load_lead with "Hphys") as "Hphys"
      | wp_apply (wp_raft_load_Term with "Hphys") as "Hphys"
      | lazymatch goal with
        | |- context [bool_decide ?P] =>
            let H := fresh "Hbd" in
            destruct (decide P) as [H|H];
            [rewrite (bool_decide_eq_true_2 P H) | rewrite (bool_decide_eq_false_2 P H)]
        end ].

  (** [MsgPreVote] with [m.Term > r.Term]: the lease check passes
      ([checkQuorum] is off), and a pre-vote **never** steps the node down.
      [canVote] holds by its third disjunct ([MsgPreVote] for a future
      term).  The answer is a [MsgPreVoteResp]: granted at [m.Term] if the
      candidate's log is up to date, else rejected at [r.Term]; nothing is
      recorded either way.  Both are free messages: [step_send_free].  The
      rejection's [Term] is the node's own, which [send] needs non-zero:
      at term [0] the candidate is up to date (the premise [Hutd0]). *)
  Lemma wp_Step_MsgPreVote_gt r id s (m : raftpb.Message.t) :
    m.(raftpb.Message.Type') = MsgPreVote →
    m.(raftpb.Message.To') = id →
    m.(raftpb.Message.Term') ≠ W64 0 →
    m.(raftpb.Message.From') ≠ W64 0 →
    (* this file: the incoming term is strictly higher *)
    uint.Z s.(nstate.term) < uint.Z m.(raftpb.Message.Term') →
    nstate_wf s →
    (s.(nstate.term) = W64 0 →
     plog_up_to_date s.(nstate.logst).(logstate.prev)
       (s.(nstate.logst).(logstate.sents) ++ s.(nstate.logst).(logstate.uents))
       (raft.entryID.mk m.(raftpb.Message.LogTerm') m.(raftpb.Message.Index')) = true) →
    {{{ is_pkg_init raft ∗
        "Hphys" ∷ own_raft_phys cfg r id s ∗
        "#Hctx" ∷ (∃ ctx, m.(raftpb.Message.Context') ↦*□ ctx ∗
                          ⌜ ctx ≠ campaignTransfer ⌝)
    }}}
      r @! (go.PointerType raft.raft) @! "Step" #m
    {{{ (err : error.t) s', RET #err;
        "Hphys" ∷ own_raft_phys cfg r id s' ∗
        "%Hwf'" ∷ ⌜ nstate_wf s' ⌝ ∗
        "%Hrefines" ∷ ⌜ step cfg id (to_pstate s) [] (to_pstate s') ⌝ ∗
        "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.
  Proof.
    intros Hty Hto Hterm Hfnz Hgt0 Hwf Hutd0.
    assert (Hty17 : m.(raftpb.Message.Type') = W32 17) by (rewrite Hty //).
    wp_start as "@". wp_auto.
    wp_apply wp_traceReceiveMessage. try wp_auto.
    (* [m.Term ≠ 0], so the first arm of the term preamble is skipped. *)
    assert (bool_decide (m.(raftpb.Message.Term') = W64 0) = false) as Hz
      by by apply bool_decide_eq_false_2.
    rewrite Hz. rewrite bool_decide_eq_false_2; last done. try wp_auto.
    wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
    assert (bool_decide (uint.Z s.(nstate.term) <
                         uint.Z m.(raftpb.Message.Term')) = true) as Hb
      by by apply bool_decide_eq_true_2.
    rewrite Hb. rewrite bool_decide_eq_true_2 //. try wp_auto.
    (* [MsgVote || MsgPreVote]: the lease check *)
    rewrite (bool_decide_eq_false_2 (m.(raftpb.Message.Type') = W32 5));
      last (rewrite Hty17; w32_ne).
    try wp_auto.
    rewrite (bool_decide_eq_true_2 (m.(raftpb.Message.Type') = W32 17)); last exact Hty17.
    try wp_auto.
    (* [force] is false (not a leader transfer) and [inLease] is false (no
       check-quorum), so the lease check does not drop the message. *)
    iDestruct "Hctx" as (ctx) "[Hctx_sl %Hctx_ne]".
    wp_apply wp_string_to_bytes as "%ct_sl [ct_sl ct_cap]".
    wp_apply (wp_Equal _ _ DfracDiscarded (DfracOwn 1) ctx ("CampaignTransfer"%go)
                with "[$Hctx_sl $ct_sl]") as "[_ ct_sl2]".
    wp_apply (wp_raft_load_checkQuorum with "Hphys") as "Hphys".
    assert (bool_decide (ctx = "CampaignTransfer"%go) = false) as Hnf
      by by apply bool_decide_eq_false_2.
    rewrite Hnf. try wp_auto.
    (* the step-down switch: [MsgPreVote], so nothing *)
    rewrite (bool_decide_eq_true_2 (m.(raftpb.Message.Type') = W32 17)); last exact Hty17.
    rewrite bool_decide_eq_true_2 //. try wp_auto.
    (* the type switch: not MsgHup / MsgStorageAppendResp /
       MsgStorageApplyResp, but MsgPreVote *)
    rewrite Hty17 bool_decide_eq_false_2; last w32_ne. try wp_auto.
    (* [canVote]: true by its third disjunct, whichever way the first two go;
       the evaluation is joined *)
    wp_bind (if: _ then _ else _)%E.
    iApply (wp_wand _ _ _
      (λ v, ⌜ v = #true ⌝ ∗ own_raft_phys cfg r id s ∗ m_ptr ↦ m ∗ r_ptr ↦ r)%I
      with "[Hphys m r]").
    { repeat cv_step.
      all: iSplitR; [iPureIntro; first [done | exfalso; lia | by exfalso] | iFrame]. }
    iIntros (v) "(-> & Hphys & m & r)". try wp_auto.
    (* [lastEntryID], then [isUpToDate] *)
    wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
    wp_hidden (iDestruct (own_raft_phys_log_same with "Hphys")
      as "(Hlog1 & Hback)").
    wp_apply (wp_raftLog__lastEntryID _ _ with "[$Hlog1]") as "%lastID [Hlog1 _]".
    wp_hidden (iDestruct ("Hback" with "Hlog1") as "Hphys").
    wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
    wp_hidden (iDestruct (own_raft_phys_log_same with "Hphys")
      as "(Hlog1 & Hback)").
    wp_apply (wp_raftLog__isUpToDate _ _ _ with "[$Hlog1]") as "%uptodate [Hlog1 %Hutd]".
    wp_hidden (iDestruct ("Hback" with "Hlog1") as "Hphys").
    destruct uptodate.
    + (* up to date: grant at [m.Term], recording nothing *)
      try wp_auto.
      (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_apply (wp_raft_load_Vote with "Hphys") as "Hphys"; wp_apply (wp_raft_load_Term with "Hphys") as "Hphys"; wp_raft_log).
      wp_apply P.wp_voteRespMsgType; first by right.
      wp_apply (P.wp_raft__send _ _ _ _ _ [] with "[$Hphys]") as "Hphys".
      { done. }
      { left; exists mtype.PreVoteResp; split_and!;
          [by right; right; right | apply mtype_of_MsgPreVoteResp | done
          | intros [Hc|Hc]; revert Hc; w32_ne | done]. }
      { iSplitR; [iApply own_slice_nil | iApply send_no_snap; simpl; w32_ne]. }
      (* not a [MsgVote]: no vote recorded *)
      rewrite (bool_decide_eq_false_2 (m.(raftpb.Message.Type') = W32 5));
        last (rewrite Hty17; w32_ne).
      try wp_auto.
      iApply ("HΦ" $! interface.nil _). iFrame "Hphys".
      iPureIntro. split; first by apply nstate_wf_send_msgs. split; last done.
      rewrite to_pstate_send_msgs. apply step_send_free; [by right|done].
    + (* behind: reject at [r.Term], which is not [0] *)
      assert (Hs0 : s.(nstate.term) ≠ W64 0).
      { intros H0. specialize (Hutd0 H0). congruence. }
      try wp_auto.
      (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_apply (wp_raft_load_Vote with "Hphys") as "Hphys"; wp_apply (wp_raft_load_Term with "Hphys") as "Hphys"; wp_raft_log).
      wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
      wp_apply P.wp_voteRespMsgType; first by right.
      wp_apply (P.wp_raft__send _ _ _ _ _ [] with "[$Hphys]") as "Hphys".
      { done. }
      { left; exists mtype.PreVoteResp; split_and!;
          [by right; right; right | apply mtype_of_MsgPreVoteResp | (simpl; exact Hs0)
          | intros [Hc|Hc]; revert Hc; w32_ne | done]. }
      { iSplitR; [iApply own_slice_nil | iApply send_no_snap; simpl; w32_ne]. }
      iApply ("HΦ" $! interface.nil _). iFrame "Hphys".
      iPureIntro. split; first by apply nstate_wf_send_msgs. split; last done.
      rewrite to_pstate_send_msgs. apply step_send_free; [by right|done].
  Qed.

End branches.

End StepMsgPreVoteGt.
