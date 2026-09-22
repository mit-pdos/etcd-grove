(** One case of [Step]'s [MsgVote] branch with [m.Term ≤ r.Term], in its own
    file so that it checks in parallel with the others -- see
    [proof_raft__Step_MsgVote_le.v], which combines them, and
    [notes/decisions.md] (2026-09-17; 2026-09-18 for why this directory
    exists).  Proof structure, not specification:
    no [Module Type], no [Parameter]; only [proof_raft__Step_MsgVote_le.v]
    may [Require] this file. *)
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__Step.

Module StepMsgVoteLt (P : STEP_POSTULATES).
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

  (** [MsgVote] with [m.Term < r.Term]: a stale vote request, dropped
      silently after the log line. *)
  Lemma wp_Step_MsgVote_lt r id s (m : raftpb.Message.t) :
    m.(raftpb.Message.Type') = MsgVote →
    m.(raftpb.Message.To') = id →
    m.(raftpb.Message.Term') ≠ W64 0 →
    (* [send] stamps the sender's id into [From], and node ids are nonzero *)
    m.(raftpb.Message.From') ≠ W64 0 →
    (* this file: the incoming term is stale, so the message is dropped *)
    uint.Z m.(raftpb.Message.Term') < uint.Z s.(nstate.term) →
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
    intros Hty Hto Hterm Hfnz Hlt0 Hwf.
    wp_start_folded as "@". iNamed "Hphys". wp_start_unfold. wp_auto.
    assert (Hle : ¬ (uint.Z rv.(raft.raft.Term') < uint.Z m.(raftpb.Message.Term')))
      by (rewrite Hterm0; lia).
    assert (Hlt : uint.Z m.(raftpb.Message.Term') < uint.Z rv.(raft.raft.Term'))
      by (rewrite Hterm0; exact Hlt0).
    wp_apply (wp_traceReceiveMessage with "[$Hmisc]") as "Hmisc".
    (* [m.Term ≠ 0], so the first arm of the term preamble is skipped. *)
    assert (bool_decide (m.(raftpb.Message.Term') = W64 0) = false) as Hz
    by by apply bool_decide_eq_false_2.
    rewrite Hz. rewrite bool_decide_eq_false_2; last done. wp_auto.
      assert (bool_decide (uint.Z rv.(raft.raft.Term') <
                           uint.Z m.(raftpb.Message.Term')) = false) as Hb
        by by apply bool_decide_eq_false_2.
      rewrite Hb. rewrite bool_decide_eq_false_2; last done. wp_auto.
        assert (bool_decide (uint.Z m.(raftpb.Message.Term') <
                             uint.Z rv.(raft.raft.Term')) = true) as Hb2
          by by apply bool_decide_eq_true_2.
        rewrite Hb2. rewrite bool_decide_eq_true_2 //. wp_auto.
        rewrite HnoCheckQuorum. wp_auto.
        rewrite HnoPreVote. wp_auto.
        (* not a MsgPreVote *)
        rewrite (bool_decide_eq_false_2 (m.(raftpb.Message.Type') = W32 17));
          last (rewrite Hty /MsgVote; w32_ne).
        wp_auto.
        (* not a MsgStorageAppendResp either, so the message is just logged *)
        rewrite (bool_decide_eq_false_2 (m.(raftpb.Message.Type') = W32 20));
          last (rewrite Hty /MsgVote; w32_ne).
        wp_auto.
        wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
        wp_auto. rewrite Hlok.
        wp_apply (wp_Logger__logf with "Hlogger").
        { solve_log_method. }
        (* nothing was sent and nothing changed: dropping is [step_refl]. *)
        iAssert (own_raft_phys cfg r id s)
          with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]"
          as "Hphys".
        { iApply (own_raft_phys_intro with
          "Hr Hlogger Hprs Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc"); done. }
        iApply ("HΦ" $! interface.nil s). iFrame "Hphys".
        iPureIntro. split; first exact Hwf. split; last done. exists [].
        split; [recv_elem|apply step_drop].
  Qed.

End branches.

End StepMsgVoteLt.
