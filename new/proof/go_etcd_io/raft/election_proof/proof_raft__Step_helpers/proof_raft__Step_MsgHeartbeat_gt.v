(** One term case of [Step]'s [MsgHeartbeat] branch (the incoming term is higher: [becomeFollower(m.Term, m.From)], then [stepFollower]), in its own file
    so that it checks in parallel with the others; [proof_raft__Step_MsgHeartbeat.v]
    combines them.  Proof structure, not specification: no [Module Type], no
    [Parameter]; only files in this directory may [Require] it. *)
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_repl_lemmas.

Module StepMsgHeartbeatGt (P : STEP_POSTULATES).
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

  Lemma wp_Step_MsgHeartbeat_gt r id s (m : raftpb.Message.t) (ents : list raftpb.Entry.t) :
    m.(raftpb.Message.Type') = MsgHeartbeat →
    m.(raftpb.Message.To') = id →
    m.(raftpb.Message.Term') ≠ W64 0 →
    m.(raftpb.Message.From') ≠ W64 0 →
    m.(raftpb.Message.From') ≠ id →
    id ∈ cfg →
    nstate_wf s →
    (* protocol fact (heartbeat_commit_le_last) *)
    (uint.Z m.(raftpb.Message.Commit')
       ≤ plog_last_index_Z s.(nstate.logst).(logstate.prev)
           (s.(nstate.logst).(logstate.sents) ++ s.(nstate.logst).(logstate.uents)))%Z →
    (* this file: the incoming term is higher: [becomeFollower(m.Term, m.From)], then [stepFollower] *)
    uint.Z s.(nstate.term) < uint.Z m.(raftpb.Message.Term') →
    {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s ∗
        "#Hents" ∷ m.(raftpb.Message.Entries') ↦*□ ents }}}
      r @! (go.PointerType raft.raft) @! "Step" #m
    {{{ (err : error.t) s', RET #err;
        "Hphys" ∷ own_raft_phys cfg r id s' ∗
        "%Hwf'" ∷ ⌜ nstate_wf s' ⌝ ∗
        "%Hrefines" ∷ ⌜ ∃ recv,
            (∀ m', m' ∈ recv → m' = abs_msg mtype.Heartbeat m ents) ∧
            step cfg id (to_pstate s) recv (to_pstate s') ⌝ ∗
        "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.
  Proof.
    intros Hty Hto Hterm Hfnz Hfid Hcfg Hwf Hcommit Hgt.
    assert (Hty8 : m.(raftpb.Message.Type') = W32 8) by (rewrite Hty //).
    assert (Hn17 : bool_decide (m.(raftpb.Message.Type') = W32 17) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty8; w32_ne).
    assert (Hn18 : bool_decide (m.(raftpb.Message.Type') = W32 18) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty8; w32_ne).
    assert (Hn5 : bool_decide (m.(raftpb.Message.Type') = W32 5) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty8; w32_ne).
    assert (Hn0 : bool_decide (m.(raftpb.Message.Type') = W32 0) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty8; w32_ne).
    assert (Hn20 : bool_decide (m.(raftpb.Message.Type') = W32 20) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty8; w32_ne).
    assert (Hn22 : bool_decide (m.(raftpb.Message.Type') = W32 22) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty8; w32_ne).
    assert (Hn3 : bool_decide (m.(raftpb.Message.Type') = W32 3) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty8; w32_ne).
    assert (Hy8 : bool_decide (m.(raftpb.Message.Type') = W32 8) = true)
      by (apply bool_decide_eq_true_2; exact Hty8).
    assert (Hn7 : bool_decide (m.(raftpb.Message.Type') = W32 7) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty8; w32_ne).
    assert (Htf : bool_decide (true = false) = false) by done.
    wp_start_folded as "@". wp_start_unfold. wp_auto.
    wp_apply wp_traceReceiveMessage. try wp_auto.
    assert (bool_decide (m.(raftpb.Message.Term') = W64 0) = false) as Hz
      by by apply bool_decide_eq_false_2.
    rewrite Hz. rewrite bool_decide_eq_false_2; last done. wp_auto.
    wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
    assert (bool_decide (uint.Z s.(nstate.term) <
                         uint.Z m.(raftpb.Message.Term')) = true) as Hb
      by by apply bool_decide_eq_true_2.
    rewrite Hb. rewrite bool_decide_eq_true_2 //. wp_auto.
    (* (Type == MsgVote) || (Type == MsgPreVote): both false *)
    rewrite Hn5. wp_auto.
    rewrite Hn17. wp_auto.
    (* the switch on MsgPreVote / MsgPreVoteResp *)
    rewrite Hn17 Htf. wp_auto.
    rewrite Hn18. wp_auto.
    (* "received a message with higher term" *)
    (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_apply (wp_raft_load_Term with "Hphys") as "Hphys"; wp_raft_log).
    (* MsgApp || MsgHeartbeat || MsgSnap: the second holds *)
    rewrite Hn3. wp_auto.
    rewrite Hy8. wp_auto.
    (* becomeFollower(m.Term, m.From): a leader's message *)
    wp_apply (P.wp_raft__becomeFollower _ _ _ _ _ _ with "[$Hphys]")
      as "%pvs Hphys".
    rewrite Hn0. wp_auto.
    rewrite Hn20. wp_auto.
    rewrite Hn22. wp_auto.
    rewrite Hn17. wp_auto.
    rewrite Hn5. wp_auto.
    wp_load_step.
    assert ((become_follower s m.(raftpb.Message.Term') m.(raftpb.Message.From')
               <| nstate.prvals := pvs |>).(nstate.stepfn)
            = functions raft.stepFollower []) as Hsf by done.
    rewrite Hsf.
    wp_apply (P.wp_stepFollower _ _ _ _ _ ents with "[$Hphys]").
    { do 3 right; left. exact Hty. }
    { intros Hc. exfalso. rewrite Hty8 in Hc. revert Hc. w32_ne. }
    { intros Hc. exfalso. rewrite Hty8 in Hc. revert Hc. w32_ne. }
    { intros _. split; [exact Hcommit|exact Hfid]. }
    { iIntros "%Hc". exfalso. rewrite Hty8 in Hc.
      destruct Hc as [Hc|Hc]; revert Hc; w32_ne. }
    iIntros (err s1 dropped) "(Hphys & %Hres & Herrn)".
    apply follower_step_result_heartbeat in Hres as [-> ->]; last exact Hty.
    iDestruct "Herrn" as %Herrn. rewrite Herrn. wp_auto.
    iApply ("HΦ" $! interface.nil _). iFrame "Hphys". iPureIntro.
    split; first done.
    split; last done.
    exists ([abs_msg mtype.Heartbeat m ents] ++ [abs_msg mtype.Heartbeat m ents]).
    split; first recv_elem.
    eapply step_trans.
    { apply (step_higher_term_leader cfg id (to_pstate s) mtype.Heartbeat m ents); done. }
    apply (step_handle_heartbeat cfg id _ _ m ents
             (adopt_after_stepdown s m.(raftpb.Message.Term') m.(raftpb.Message.From') pvs)).
    - exact Hto.
    - done.
    - done.
    - exact Hcommit.
  Qed.

End branches.

End StepMsgHeartbeatGt.
