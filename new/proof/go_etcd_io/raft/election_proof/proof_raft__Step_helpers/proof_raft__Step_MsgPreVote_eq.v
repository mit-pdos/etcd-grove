(** One term case of [Step]'s [MsgPreVote] branch (2026-10-04): the
    incoming term is the node's own.  In its own file so that it checks in
    parallel with the others; [proof_raft__Step_MsgPreVote.v] combines
    them.  Proof structure, not specification: no [Module Type], no
    [Parameter]; only files in this directory may [Require] it. *)
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_prevote_lemmas.

Module StepMsgPreVoteEq (P : STEP_POSTULATES).
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

  (** [MsgPreVote] with [m.Term = r.Term]: the preamble does nothing, and
      the vote arm answers with a [MsgPreVoteResp] -- granted at [m.Term]
      or rejected at [r.Term], the same term -- recording nothing.  What
      [canVote] evaluates to does not matter to the protocol: either answer
      is a free message ([step_send_free]). *)
  Lemma wp_Step_MsgPreVote_eq r id s (m : raftpb.Message.t) :
    m.(raftpb.Message.Type') = MsgPreVote →
    m.(raftpb.Message.To') = id →
    m.(raftpb.Message.Term') ≠ W64 0 →
    m.(raftpb.Message.From') ≠ W64 0 →
    (* this file: the same term *)
    m.(raftpb.Message.Term') = s.(nstate.term) →
    nstate_wf s →
    {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s }}}
      r @! (go.PointerType raft.raft) @! "Step" #m
    {{{ (err : error.t) s', RET #err;
        "Hphys" ∷ own_raft_phys cfg r id s' ∗
        "%Hwf'" ∷ ⌜ nstate_wf s' ⌝ ∗
        "%Hrefines" ∷ ⌜ step cfg id (to_pstate s) [] (to_pstate s') ⌝ ∗
        "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.
  Proof.
    intros Hty Hto Hterm Hfnz Heq0 Hwf.
    assert (Hty17 : m.(raftpb.Message.Type') = W32 17) by (rewrite Hty //).
    wp_start_folded as "@". wp_start_unfold. wp_auto.
    wp_apply wp_traceReceiveMessage. try wp_auto.
    assert (bool_decide (m.(raftpb.Message.Term') = W64 0) = false) as Hz
      by by apply bool_decide_eq_false_2.
    rewrite Hz. rewrite bool_decide_eq_false_2; last done. wp_auto.
    wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
    assert (bool_decide (uint.Z s.(nstate.term) <
                         uint.Z m.(raftpb.Message.Term')) = false) as Hb
      by (apply bool_decide_eq_false_2; rewrite Heq0; lia).
    rewrite Hb. rewrite bool_decide_eq_false_2; last done. wp_auto.
    wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
    assert (bool_decide (uint.Z m.(raftpb.Message.Term') <
                         uint.Z s.(nstate.term)) = false) as Hb2
      by (apply bool_decide_eq_false_2; rewrite Heq0; lia).
    rewrite Hb2. rewrite bool_decide_eq_false_2; last done. wp_auto.
    (* the type switch: not MsgHup / MsgStorageAppendResp /
       MsgStorageApplyResp, but MsgPreVote *)
    rewrite Hty17 bool_decide_eq_false_2; last w32_ne. wp_auto.
    (* [canVote], whatever it is; the evaluation is joined *)
    wp_bind (if: _ then _ else _)%E.
    iApply (wp_wand _ _ _
      (λ v, ⌜ ∃ b : bool, v = #b ⌝ ∗ own_raft_phys cfg r id s ∗ m_ptr ↦ m ∗ r_ptr ↦ r)%I
      with "[Hphys m r]").
    { repeat cv_step.
      all: iSplitR; [iPureIntro; eexists; done | iFrame]. }
    iIntros (v) "([%cv ->] & Hphys & m & r)". try wp_auto.
    wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
    wp_hidden (iDestruct (own_raft_phys_log_same with "Hphys")
      as "(Hlog1 & Hback)").
    wp_apply (wp_raftLog__lastEntryID _ _ with "[$Hlog1]") as "%lastID [Hlog1 _]".
    wp_hidden (iDestruct ("Hback" with "Hlog1") as "Hphys").
    (* [canVote && isUpToDate(…)]: the reject arm is reached two ways *)
    destruct cv; try wp_auto.
    - wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
      wp_hidden (iDestruct (own_raft_phys_log_same with "Hphys")
        as "(Hlog1 & Hback)").
      wp_apply (wp_raftLog__isUpToDate _ _ _ with "[$Hlog1]") as "%uptodate [Hlog1 %Hutd]".
      wp_hidden (iDestruct ("Hback" with "Hlog1") as "Hphys").
      destruct uptodate.
      + (* grant at [m.Term], recording nothing *)
        try wp_auto.
        (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_apply (wp_raft_load_Vote with "Hphys") as "Hphys"; wp_apply (wp_raft_load_Term with "Hphys") as "Hphys"; wp_raft_log).
        wp_apply P.wp_voteRespMsgType; first by right.
        wp_apply (P.wp_raft__send _ _ _ _ _ [] with "[$Hphys]") as "Hphys".
        { by left. }
        { left; exists mtype.PreVoteResp; split_and!;
            [by right; right; right | apply mtype_of_MsgPreVoteResp | done
            | intros [Hc|Hc]; revert Hc; w32_ne | done]. }
        { iSplitR; [iApply own_slice_nil | iApply send_no_snap; simpl; w32_ne]. }
        rewrite (bool_decide_eq_false_2 (m.(raftpb.Message.Type') = W32 5));
          last (rewrite Hty17; w32_ne).
        try wp_auto.
        iApply ("HΦ" $! interface.nil _). iFrame "Hphys".
        iPureIntro. split; first by apply nstate_wf_send_msgs. split; last done.
        rewrite to_pstate_send_msgs. apply step_send_free; [by right|done].
      + (* behind: reject *)
        try wp_auto.
        (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_apply (wp_raft_load_Vote with "Hphys") as "Hphys"; wp_apply (wp_raft_load_Term with "Hphys") as "Hphys"; wp_raft_log).
        wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
        wp_apply P.wp_voteRespMsgType; first by right.
        wp_apply (P.wp_raft__send _ _ _ _ _ [] with "[$Hphys]") as "Hphys".
        { by left. }
        { left; exists mtype.PreVoteResp; split_and!;
            [by right; right; right | apply mtype_of_MsgPreVoteResp | (simpl; congruence)
            | intros [Hc|Hc]; revert Hc; w32_ne | done]. }
        { iSplitR; [iApply own_slice_nil | iApply send_no_snap; simpl; w32_ne]. }
        iApply ("HΦ" $! interface.nil _). iFrame "Hphys".
        iPureIntro. split; first by apply nstate_wf_send_msgs. split; last done.
        rewrite to_pstate_send_msgs. apply step_send_free; [by right|done].
    - (* cannot vote: reject *)
      (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_apply (wp_raft_load_Vote with "Hphys") as "Hphys"; wp_apply (wp_raft_load_Term with "Hphys") as "Hphys"; wp_raft_log).
      wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
      wp_apply P.wp_voteRespMsgType; first by right.
      wp_apply (P.wp_raft__send _ _ _ _ _ [] with "[$Hphys]") as "Hphys".
      { by left. }
      { left; exists mtype.PreVoteResp; split_and!;
          [by right; right; right | apply mtype_of_MsgPreVoteResp | (simpl; congruence)
          | intros [Hc|Hc]; revert Hc; w32_ne | done]. }
      { iSplitR; [iApply own_slice_nil | iApply send_no_snap; simpl; w32_ne]. }
      iApply ("HΦ" $! interface.nil _). iFrame "Hphys".
      iPureIntro. split; first by apply nstate_wf_send_msgs. split; last done.
      rewrite to_pstate_send_msgs. apply step_send_free; [by right|done].
  Qed.

End branches.

End StepMsgPreVoteEq.
