(** The higher-term case of [Step]'s [MsgAppResp] and [MsgHeartbeatResp]
    branches, for both types at once (they take the same path through the
    preamble and reach no arm of [stepFollower]), in its own file so that
    it checks in parallel with the other term cases -- see
    [proof_raft__Step_MsgAppResp.v] and [proof_raft__Step_MsgHeartbeatResp.v],
    which combine them.  Proof structure, not specification: no
    [Module Type], no [Parameter]; only files in this directory may
    [Require] it. *)
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_resp_lemmas.

Module StepRespGt (P : STEP_POSTULATES).
Import P.

Section branches.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).

Implicit Type s : nstate.t.

  Local Ltac recv_elem :=
    intros ? Hin;
    rewrite ?elem_of_app ?list_elem_of_singleton ?elem_of_nil in Hin;
    naive_solver.

  Local Ltac ne_ty Hty :=
    apply bool_decide_eq_false_2;
    destruct Hty as [[Ht _]|[Ht _]]; rewrite Ht; w32_ne.

  Local Ltac wp_load_step :=
    wp_bind (![raft.stepFunc] _)%E;
    iApply (wp_raft_load_step with "Hphys"); iIntros "!> Hphys".

  (** [m.Term > r.Term] for a [MsgAppResp] or [MsgHeartbeatResp]: neither
      is [from_leader], so the preamble runs [becomeFollower(m.Term, None)];
      the type switch then reaches its default arm, [r.step(m)], which is
      [stepFollower] after the step-down, and [stepFollower] has no arm for
      either type.  One [step_higher_term]. *)
  Lemma wp_Step_Resp_gt r id s (m : raftpb.Message.t)
      (ents : list raftpb.Entry.t) (ty : mtype.t) :
    (m.(raftpb.Message.Type') = MsgAppResp ∧ ty = mtype.AppResp) ∨
    (m.(raftpb.Message.Type') = MsgHeartbeatResp ∧ ty = mtype.HeartbeatResp) →
    m.(raftpb.Message.To') = id →
    m.(raftpb.Message.Term') ≠ W64 0 →
    uint.Z s.(nstate.term) < uint.Z m.(raftpb.Message.Term') →
    nstate_wf s →
    {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s }}}
      r @! (go.PointerType raft.raft) @! "Step" #m
    {{{ (err : error.t) s', RET #err;
        "Hphys" ∷ own_raft_phys cfg r id s' ∗
        "%Hwf'" ∷ ⌜ nstate_wf s' ⌝ ∗
        "%Hrefines" ∷ ⌜ ∃ recv,
            (∀ m', m' ∈ recv → m' = abs_msg ty m ents) ∧
            step cfg id (to_pstate s) recv (to_pstate s') ⌝ ∗
        "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.
  Proof.
    intros Hty Hto Hterm Hgt Hwf.
    assert (Hfl : from_leader ty = false) by (destruct Hty as [[_ ->]|[_ ->]]; done).
    assert (Hty3 : m.(raftpb.Message.Type') = MsgBeat ∨
                   m.(raftpb.Message.Type') = MsgAppResp ∨
                   m.(raftpb.Message.Type') = MsgHeartbeatResp)
      by (destruct Hty as [[Ht _]|[Ht _]]; auto).
    (* the type tests this branch meets, hoisted (see
       proof_raft__Step_MsgVoteResp.v for why) *)
    assert (Hn17 : bool_decide (m.(raftpb.Message.Type') = W32 17) = false) by ne_ty Hty.
    assert (Hn18 : bool_decide (m.(raftpb.Message.Type') = W32 18) = false) by ne_ty Hty.
    assert (Hn5 : bool_decide (m.(raftpb.Message.Type') = W32 5) = false) by ne_ty Hty.
    assert (Hn3 : bool_decide (m.(raftpb.Message.Type') = W32 3) = false) by ne_ty Hty.
    assert (Hn8 : bool_decide (m.(raftpb.Message.Type') = W32 8) = false) by ne_ty Hty.
    assert (Hn7 : bool_decide (m.(raftpb.Message.Type') = W32 7) = false) by ne_ty Hty.
    assert (Hn0 : bool_decide (m.(raftpb.Message.Type') = W32 0) = false) by ne_ty Hty.
    assert (Hn20 : bool_decide (m.(raftpb.Message.Type') = W32 20) = false) by ne_ty Hty.
    assert (Hn22 : bool_decide (m.(raftpb.Message.Type') = W32 22) = false) by ne_ty Hty.
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
    rewrite Hn17 Htf. wp_auto.
    (* not (MsgPreVoteResp && !Reject) *)
    rewrite Hn18. wp_auto.
    (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_apply (wp_raft_load_Term with "Hphys") as "Hphys"; wp_raft_log).
    (* not from a leader: not MsgApp / MsgHeartbeat / MsgSnap *)
    rewrite Hn3. wp_auto.
    rewrite Hn8. wp_auto.
    rewrite Hn7. wp_auto.
    wp_apply (P.wp_raft__becomeFollower _ _ _ _ _ _ with "[$Hphys]")
      as "%pvs Hphys".
    assert (step cfg id (to_pstate s) [abs_msg ty m ents]
              (to_pstate (become_follower s m.(raftpb.Message.Term') (W64 0)))) as Hsd.
    { rewrite to_pstate_become_follower.
      replace (W64 0) with
        (if from_leader (abs_msg ty m ents).(msg.ty)
         then (abs_msg ty m ents).(msg.from) else W64 0)
        by (rewrite /abs_msg /abs_msg_from /= Hfl //).
      replace m.(raftpb.Message.Term') with
        (abs_msg ty m ents).(msg.term) by done.
      apply step_higher_term.
      - rewrite /abs_msg /=. exact Hgt.
      - rewrite /abs_msg /=. exact Hto. }
    (* the type switch's four tests, then the default arm *)
    rewrite Hn0. wp_auto.
    rewrite Hn20. wp_auto.
    rewrite Hn22. wp_auto.
    rewrite Hn17. wp_auto.
    rewrite Hn5. wp_auto.
    wp_load_step.
    assert ((become_follower s m.(raftpb.Message.Term') (W64 0)
               <| nstate.prvals := pvs |>).(nstate.stepfn)
            = functions raft.stepFollower []) as Hsf by done.
    rewrite Hsf.
    wp_apply (P.wp_stepFollower _ _ _ _ _ [] with "[$Hphys]").
    { right; right; right; right. exact Hty3. }
    { intros Hc. exfalso. destruct Hty3 as [Ht|[Ht|Ht]]; rewrite Ht in Hc; revert Hc; w32_ne. }
    { intros Hc. exfalso. destruct Hty3 as [Ht|[Ht|Ht]]; rewrite Ht in Hc; revert Hc; w32_ne. }
    { intros Hc. exfalso. destruct Hty3 as [Ht|[Ht|Ht]]; rewrite Ht in Hc; revert Hc; w32_ne. }
    { iIntros "%Hc". exfalso.
      destruct Hc as [Hc|Hc]; destruct Hty3 as [Ht|[Ht|Ht]]; rewrite Ht in Hc;
        revert Hc; w32_ne. }
    iIntros (err s1 dropped) "(Hphys & %Hres & Herrn)".
    destruct (follower_step_result_noop _ _ _ _ _ _ Hty3 Hres) as [-> ->]. iDestruct "Herrn" as %Herrn.
    rewrite Herrn. wp_auto.
    iApply ("HΦ" $! interface.nil
              (become_follower s m.(raftpb.Message.Term') (W64 0)
                 <| nstate.prvals := pvs |>)).
    iFrame "Hphys". iPureIntro.
    split; first done.
    split; last done.
    exists [abs_msg ty m ents]. split.
    { recv_elem. }
    rewrite to_pstate_prvals_nl; last (simpl; congruence).
    exact Hsd.
  Qed.

End branches.

End StepRespGt.
