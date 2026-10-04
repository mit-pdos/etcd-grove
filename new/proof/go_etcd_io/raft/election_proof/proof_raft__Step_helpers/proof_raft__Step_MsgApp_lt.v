(** One term case of [Step]'s [MsgApp] branch (the incoming term is stale: logged and dropped), in its own file
    so that it checks in parallel with the others; [proof_raft__Step_MsgApp.v]
    combines them.  Proof structure, not specification: no [Module Type], no
    [Parameter]; only files in this directory may [Require] it. *)
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_repl_lemmas.

Module StepMsgAppLt (P : STEP_POSTULATES).
Import P.

Section branches.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).

Implicit Type s : nstate.t.

  (** [∀ m', m' ∈ recv → m' = a] for the concrete [recv] lists ([[]],
      [[a]], [[a] ++ [a]]); not [set_solver] (notes/gotchas.md). *)
  Local Ltac recv_elem :=
    intros ? Hin;
    rewrite ?elem_of_app ?list_elem_of_singleton ?elem_of_nil in Hin;
    naive_solver.

  (** The load of [r.step] in [r.step(r, m)], bound by hand: [wp_apply]
      does not find a load in function position. *)
  Local Ltac wp_load_step :=
    wp_bind (![raft.stepFunc] _)%E;
    iApply (wp_raft_load_step with "Hphys"); iIntros "!> Hphys".

  Lemma wp_Step_MsgApp_lt r id s (m : raftpb.Message.t) (ents : list raftpb.Entry.t) :
    m.(raftpb.Message.Type') = MsgApp →
    m.(raftpb.Message.To') = id →
    m.(raftpb.Message.Term') ≠ W64 0 →
    m.(raftpb.Message.From') ≠ W64 0 →
    m.(raftpb.Message.From') ≠ id →
    id ∈ cfg →
    nstate_wf s →
    (* protocol facts the dispatch derives from the ghost state (app_recv_wf, app_no_conflict_below_commit) *)
    plog_wf (raft.entryID.mk m.(raftpb.Message.LogTerm') m.(raftpb.Message.Index')) ents →
    (uint.Z m.(raftpb.Message.Index') + Z.of_nat (length ents) + 1 < 2^64)%Z →
    Forall (λ e, e.(raftpb.Entry.Type') = EntryNormal) ents →
    (* (no conflict premise: a stale message never reaches [maybeAppend]) *)
    (* this file: the incoming term is stale: logged and dropped *)
    uint.Z m.(raftpb.Message.Term') < uint.Z s.(nstate.term) →
    {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s ∗
        "#Hents" ∷ m.(raftpb.Message.Entries') ↦*□ ents ∗
        "Hcap" ∷ own_slice_cap raftpb.Entry.t m.(raftpb.Message.Entries') (DfracOwn 1) }}}
      r @! (go.PointerType raft.raft) @! "Step" #m
    {{{ (err : error.t) s', RET #err;
        "Hphys" ∷ own_raft_phys cfg r id s' ∗
        "%Hwf'" ∷ ⌜ nstate_wf s' ⌝ ∗
        "%Hrefines" ∷ ⌜ ∃ recv,
            (∀ m', m' ∈ recv → m' = abs_msg mtype.App m ents) ∧
            step cfg id (to_pstate s) recv (to_pstate s') ⌝ ∗
        "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.
  Proof.
    intros Hty Hto Hterm Hfnz Hfid Hcfg Hwf Hpwf Hnw Hnorm Hlt.
    assert (Hty3 : m.(raftpb.Message.Type') = W32 3) by (rewrite Hty //).
    assert (Hn17 : bool_decide (m.(raftpb.Message.Type') = W32 17) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty3; w32_ne).
    assert (Hn18 : bool_decide (m.(raftpb.Message.Type') = W32 18) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty3; w32_ne).
    assert (Hn5 : bool_decide (m.(raftpb.Message.Type') = W32 5) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty3; w32_ne).
    assert (Hn0 : bool_decide (m.(raftpb.Message.Type') = W32 0) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty3; w32_ne).
    assert (Hn20 : bool_decide (m.(raftpb.Message.Type') = W32 20) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty3; w32_ne).
    assert (Hn22 : bool_decide (m.(raftpb.Message.Type') = W32 22) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty3; w32_ne).
    assert (Hy3 : bool_decide (m.(raftpb.Message.Type') = W32 3) = true)
      by (apply bool_decide_eq_true_2; exact Hty3).
    assert (Hn8 : bool_decide (m.(raftpb.Message.Type') = W32 8) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty3; w32_ne).
    assert (Hn7 : bool_decide (m.(raftpb.Message.Type') = W32 7) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty3; w32_ne).
    assert (Htf : bool_decide (true = false) = false) by done.
    wp_start_folded as "@". wp_start_unfold. wp_auto.
    wp_apply wp_traceReceiveMessage. try wp_auto.
    assert (bool_decide (m.(raftpb.Message.Term') = W64 0) = false) as Hz
      by by apply bool_decide_eq_false_2.
    rewrite Hz. rewrite bool_decide_eq_false_2; last done. wp_auto.
    wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
    assert (bool_decide (uint.Z s.(nstate.term) <
                         uint.Z m.(raftpb.Message.Term')) = false) as Hb
      by (apply bool_decide_eq_false_2; lia).
    rewrite Hb Htf. wp_auto.
    wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
    assert (bool_decide (uint.Z m.(raftpb.Message.Term') <
                         uint.Z s.(nstate.term)) = true) as Hb2
      by by apply bool_decide_eq_true_2.
    rewrite Hb2. rewrite bool_decide_eq_true_2 //. wp_auto.
    (* (checkQuorum || preVote) && (MsgHeartbeat || MsgApp): [checkQuorum]
       is off; with pre-vote on, a stale leader message is answered with a
       bare [MsgAppResp] at the node's term (2026-10-04) *)
    wp_apply (wp_raft_load_checkQuorum with "Hphys") as "Hphys".
    wp_apply (wp_raft_load_preVote with "Hphys") as "Hphys".
    destruct (s.(nstate.prevote)); wp_auto.
    - rewrite Hn8. wp_auto. rewrite Hy3. wp_auto.
      wp_apply (P.wp_raft__send _ _ _ _ _ [] with "[$Hphys]") as "Hphys".
      { done. }
      { right; right; right; left. split_and!; done. }
      { iSplitR; [iApply own_slice_nil | iApply send_no_snap; simpl; w32_ne]. }
      iApply ("HΦ" $! interface.nil _). iFrame "Hphys".
      iPureIntro. split; first by apply nstate_wf_send_msgs. split; last done.
      exists []. split; first recv_elem.
      rewrite to_pstate_send_msgs. apply step_zero_ack.
    - (* not MsgPreVote, not MsgStorageAppendResp: only the log line *)
      rewrite Hn17. wp_auto.
      rewrite Hn20. wp_auto.
      (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_apply (wp_raft_load_Term with "Hphys") as "Hphys"; wp_raft_log).
      iApply ("HΦ" $! interface.nil s). iFrame "Hphys".
      iPureIntro. split; first exact Hwf. split; last done.
      exists []. split; last apply step_refl.
      recv_elem.
  Qed.

End branches.

End StepMsgAppLt.
