(** One term case of [Step]'s [MsgPreVoteResp] branch (2026-10-04): the
    incoming term is higher.  In its own file so that it checks in parallel
    with the others; [proof_raft__Step_MsgPreVoteResp.v] combines them.
    Proof structure, not specification: no [Module Type], no [Parameter];
    only files in this directory may [Require] it. *)
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_prevote_lemmas.

Module StepMsgPreVoteRespGt (P : STEP_POSTULATES).
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

  Local Ltac wp_load_step :=
    wp_bind (![raft.stepFunc] _)%E;
    iApply (wp_raft_load_step with "Hphys"); iIntros "!> Hphys".

  Local Ltac ne_ty Hty :=
    apply bool_decide_eq_false_2; rewrite Hty; w32_ne.

  (** [MsgPreVoteResp] with [m.Term > r.Term].  A *granted* one does not
      step the node down (raft.go:1104: it carries the pre-candidate's
      future term): straight to [r.step(m)], as at the current term.  A
      *rejecting* one does -- [becomeFollower(m.Term, None)], one
      [step_higher_term] (not [from_leader]) -- and then [stepFollower]
      has no arm for it. *)
  Lemma wp_Step_MsgPreVoteResp_gt r id s (m : raftpb.Message.t)
      (ents : list raftpb.Entry.t) :
    m.(raftpb.Message.Type') = MsgPreVoteResp →
    m.(raftpb.Message.To') = id →
    m.(raftpb.Message.Term') ≠ W64 0 →
    (* this file: the incoming term is strictly higher *)
    uint.Z s.(nstate.term) < uint.Z m.(raftpb.Message.Term') →
    uint.Z s.(nstate.term) + 1 < 2 ^ 64 →
    id ∈ cfg →
    nstate_wf s →
    {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s }}}
      r @! (go.PointerType raft.raft) @! "Step" #m
    {{{ (err : error.t) s', RET #err;
        "Hphys" ∷ own_raft_phys cfg r id s' ∗
        "%Hwf'" ∷ ⌜ nstate_wf s' ⌝ ∗
        "%Hrefines" ∷ ⌜ ∃ recv,
            (∀ m', m' ∈ recv → m' = abs_msg mtype.PreVoteResp m ents) ∧
            step cfg id (to_pstate s) recv (to_pstate s') ⌝ ∗
        "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.
  Proof.
    intros Hty Hto Hterm Hgt Hnw Hcfg Hwf.
    assert (Hsfw : s.(nstate.stepfn) = step_func_of s.(nstate.role)) by exact Hwf.
    assert (Hty18 : m.(raftpb.Message.Type') = W32 18) by (rewrite Hty //).
    assert (Hn17 : bool_decide (m.(raftpb.Message.Type') = W32 17) = false) by ne_ty Hty.
    assert (Hn5 : bool_decide (m.(raftpb.Message.Type') = W32 5) = false) by ne_ty Hty.
    assert (Hn0 : bool_decide (m.(raftpb.Message.Type') = W32 0) = false) by ne_ty Hty.
    assert (Hn20 : bool_decide (m.(raftpb.Message.Type') = W32 20) = false) by ne_ty Hty.
    assert (Hn22 : bool_decide (m.(raftpb.Message.Type') = W32 22) = false) by ne_ty Hty.
    assert (Hn3 : bool_decide (m.(raftpb.Message.Type') = W32 3) = false) by ne_ty Hty.
    assert (Hn8 : bool_decide (m.(raftpb.Message.Type') = W32 8) = false) by ne_ty Hty.
    assert (Hn7 : bool_decide (m.(raftpb.Message.Type') = W32 7) = false) by ne_ty Hty.
    assert (Hy18 : bool_decide (m.(raftpb.Message.Type') = W32 18) = true)
      by (apply bool_decide_eq_true_2; exact Hty18).
    assert (Htf : bool_decide (true = false) = false) by done.
    assert (Hgr : bool_decide (true = negb false) = true) by done.
    assert (Hrj : bool_decide (true = negb true) = false) by done.
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
    (* the step-down switch: not MsgPreVote; MsgPreVoteResp, and [!Reject]
       decides *)
    rewrite Hn17 Htf. wp_auto.
    rewrite Hy18. wp_auto.
    destruct (m.(raftpb.Message.Reject')) eqn:Hrej.
    + (* rejected: step down to the higher term, no leader *)
      rewrite Hrj. wp_auto.
      (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_apply (wp_raft_load_Term with "Hphys") as "Hphys"; wp_raft_log).
      rewrite Hn3. wp_auto.
      rewrite Hn8. wp_auto.
      rewrite Hn7. wp_auto.
      wp_apply (P.wp_raft__becomeFollower _ _ _ _ _ _ with "[$Hphys]")
        as "%pvs Hphys".
      assert (step cfg id (to_pstate s) [abs_msg mtype.PreVoteResp m ents]
                (to_pstate (become_follower s m.(raftpb.Message.Term') (W64 0)))) as Hsd.
      { rewrite to_pstate_become_follower.
        replace (W64 0) with
          (if from_leader (abs_msg mtype.PreVoteResp m ents).(msg.ty)
           then (abs_msg mtype.PreVoteResp m ents).(msg.from) else W64 0) by done.
        replace m.(raftpb.Message.Term') with
          (abs_msg mtype.PreVoteResp m ents).(msg.term) by done.
        apply step_higher_term.
        - rewrite /abs_msg /=. exact Hgt.
        - rewrite /abs_msg /=. exact Hto.
        - rewrite /abs_msg /=. by intros [=]. }
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
      wp_apply (P.wp_stepFollower _ _ _ _ _ [] (zero_val _) [] with "[$Hphys]").
      { do 5 right; right. exact Hty. }
      { intros Hc. exfalso. rewrite Hty18 in Hc. revert Hc. w32_ne. }
      { intros Hc. exfalso. rewrite Hty18 in Hc. revert Hc. w32_ne. }
      { intros Hc. exfalso. rewrite Hty18 in Hc. revert Hc. w32_ne. }
      { iSplitR; [step_no_snap|]. iIntros "%Hc". exfalso. rewrite Hty18 in Hc.
        destruct Hc as [Hc|Hc]; revert Hc; w32_ne. }
      iIntros (err s1 dropped) "(Hphys & %Hres & Herrn)".
      destruct (follower_step_result_prevoteresp _ _ _ _ _ _ _ Hty Hres) as [-> ->].
      iDestruct "Herrn" as %Herrn. rewrite Herrn. wp_auto.
      iApply ("HΦ" $! interface.nil
                (become_follower s m.(raftpb.Message.Term') (W64 0)
                   <| nstate.prvals := pvs |>)).
      iFrame "Hphys". iPureIntro.
      split; first done.
      split; last done.
      exists [abs_msg mtype.PreVoteResp m ents]. split.
      { recv_elem. }
      rewrite to_pstate_prvals_nl; last (simpl; congruence).
      exact Hsd.
    + (* granted: no step-down; [r.step(m)] in the current role *)
      rewrite Hgr. wp_auto.
      rewrite Hn0. wp_auto.
      rewrite Hn20. wp_auto.
      rewrite Hn22. wp_auto.
      rewrite Hn17. wp_auto.
      rewrite Hn5. wp_auto.
      wp_load_step.
      destruct s.(nstate.role) eqn:Hrole.
      * (* Follower: no arm *)
        assert (s.(nstate.stepfn) = functions raft.stepFollower []) as Hsf
          by (rewrite Hsfw ?Hrole //).
        rewrite Hsf.
        wp_apply (P.wp_stepFollower _ _ _ _ _ [] (zero_val _) [] with "[$Hphys]").
        { do 5 right; right. exact Hty. }
        { intros Hc. exfalso. rewrite Hty18 in Hc. revert Hc. w32_ne. }
        { intros Hc. exfalso. rewrite Hty18 in Hc. revert Hc. w32_ne. }
        { intros Hc. exfalso. rewrite Hty18 in Hc. revert Hc. w32_ne. }
        { iSplitR; [step_no_snap|]. iIntros "%Hc". exfalso. rewrite Hty18 in Hc.
          destruct Hc as [Hc|Hc]; revert Hc; w32_ne. }
        iIntros (err s1 dropped) "(Hphys & %Hres & Herrn)".
        destruct (follower_step_result_prevoteresp _ _ _ _ _ _ _ Hty Hres) as [-> ->].
        iDestruct "Herrn" as %Herrn. rewrite Herrn. wp_auto.
        iApply ("HΦ" $! interface.nil s). iFrame "Hphys".
        iPureIntro. split; first exact Hwf. split; last done.
        exists []. split; last apply step_refl.
        recv_elem.
      * (* Candidate: [myVoteRespType] is [MsgVoteResp]; a stale pre-vote
           response is ignored *)
        assert (s.(nstate.stepfn) = functions raft.stepCandidate []) as Hsf
          by (rewrite Hsfw ?Hrole //).
        rewrite Hsf.
        wp_apply (P.wp_stepCandidate _ _ _ _ _ [] (zero_val _) [] with "[$Hphys]").
        { do 5 right; right. exact Hty. }
        { intros Hc. exfalso. rewrite Hty18 in Hc.
          destruct Hc as [Hc|[Hc|[Hc|Hc]]]; revert Hc; w32_ne. }
        { by left. }
        { exact Hcfg. }
        { intros Hc. exfalso. rewrite Hty18 in Hc. revert Hc. w32_ne. }
        { intros Hc. exfalso. rewrite Hty18 in Hc. revert Hc. w32_ne. }
        { intros _ _. exact Hnw. }
        { iSplitR; [step_no_snap|]. iIntros "%Hc". exfalso. rewrite Hty18 in Hc. revert Hc. w32_ne. }
        iIntros (err s1 dropped) "(Hphys & %Hres & Herrn)".
        destruct (candidate_step_result_prevoteresp cfg _ _ _ _ _ _ _ Hty (or_introl Hrole)
                    Hcfg Hnw Hwf Hres) as (-> & Hwf1 & Hst).
        iDestruct "Herrn" as %Herrn. rewrite Herrn. wp_auto.
        iApply ("HΦ" $! interface.nil s1). iFrame "Hphys".
        iPureIntro. split; first exact Hwf1. split; last done.
        exists []. split; [recv_elem|exact Hst].
      * (* Leader: no arm *)
        assert (s.(nstate.stepfn) = functions raft.stepLeader []) as Hsf
          by (rewrite Hsfw ?Hrole //).
        rewrite Hsf.
        iAssert (⌜ m.(raftpb.Message.Type') = MsgHeartbeatResp ⌝ -∗
                 m.(raftpb.Message.Context') ↦*□ ([] : list w8))%I as "Hctx0".
        { iIntros "%Hc". exfalso. revert Hc. rewrite Hty18. w32_ne. }
        iAssert (⌜ m.(raftpb.Message.Type') = MsgProp ⌝ -∗
                 m.(raftpb.Message.Entries') ↦* ([] : list raftpb.Entry.t))%I as "Hents0".
        { iIntros "%Hc". exfalso. revert Hc. rewrite Hty18. w32_ne. }
        wp_apply (P.wp_stepLeader _ _ _ _ _ [] with "[$Hphys $Hctx0 $Hents0]")
          as (err s' dropped) "(Hphys & %Hres & Herrn & _)".
        { do 6 right; right. exact Hty. }
        { exact Hrole. }
        { exact Hcfg. }
        { intros Hc. exfalso. revert Hc. rewrite Hty18. w32_ne. }
        { intros [Hc|[Hc _]]; exfalso; revert Hc; rewrite Hty18; w32_ne. }
        { intros Hc. exfalso. revert Hc. rewrite Hty18. w32_ne. }
        destruct (leader_step_result_prevoteresp cfg _ _ _ _ _ _ Hty Hres) as [-> ->].
        iDestruct "Herrn" as %Herrn. rewrite Herrn. wp_auto.
        iApply ("HΦ" $! interface.nil s). iFrame "Hphys".
        iPureIntro. split; first exact Hwf. split; last done.
        exists []. split; last apply step_refl.
        recv_elem.
      * (* PreCandidate: the pre-vote tally *)
        assert (s.(nstate.stepfn) = functions raft.stepCandidate []) as Hsf
          by (rewrite Hsfw ?Hrole //).
        rewrite Hsf.
        wp_apply (P.wp_stepCandidate _ _ _ _ _ [] (zero_val _) [] with "[$Hphys]").
        { do 5 right; right. exact Hty. }
        { intros Hc. exfalso. rewrite Hty18 in Hc.
          destruct Hc as [Hc|[Hc|[Hc|Hc]]]; revert Hc; w32_ne. }
        { by right. }
        { exact Hcfg. }
        { intros Hc. exfalso. rewrite Hty18 in Hc. revert Hc. w32_ne. }
        { intros Hc. exfalso. rewrite Hty18 in Hc. revert Hc. w32_ne. }
        { intros _ _. exact Hnw. }
        { iSplitR; [step_no_snap|]. iIntros "%Hc". exfalso. rewrite Hty18 in Hc. revert Hc. w32_ne. }
        iIntros (err s1 dropped) "(Hphys & %Hres & Herrn)".
        destruct (candidate_step_result_prevoteresp cfg _ _ _ _ _ _ _ Hty (or_intror Hrole)
                    Hcfg Hnw Hwf Hres) as (-> & Hwf1 & Hst).
        iDestruct "Herrn" as %Herrn. rewrite Herrn. wp_auto.
        iApply ("HΦ" $! interface.nil s1). iFrame "Hphys".
        iPureIntro. split; first exact Hwf1. split; last done.
        exists []. split; [recv_elem|exact Hst].
  Qed.

End branches.

End StepMsgPreVoteRespGt.
