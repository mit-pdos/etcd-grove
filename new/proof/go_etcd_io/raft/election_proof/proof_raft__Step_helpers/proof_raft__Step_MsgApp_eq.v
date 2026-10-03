(** One term case of [Step]'s [MsgApp] branch (the current term: [r.step(m)], by role), in its own file
    so that it checks in parallel with the others; [proof_raft__Step_MsgApp.v]
    combines them.  Proof structure, not specification: no [Module Type], no
    [Parameter]; only files in this directory may [Require] it. *)
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_repl_lemmas.

Module StepMsgAppEq (P : STEP_POSTULATES).
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

  Lemma wp_Step_MsgApp_eq r id s (m : raftpb.Message.t) (ents : list raftpb.Entry.t) :
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
    (let ls := s.(nstate.logst) in
     let es := ls.(logstate.sents) ++ ls.(logstate.uents) in
     (uint.Z ls.(logstate.committed) ≤ uint.Z m.(raftpb.Message.Index'))%Z →
     plog_matches ls.(logstate.prev) es
       (raft.entryID.mk m.(raftpb.Message.LogTerm') m.(raftpb.Message.Index')) →
     plog_find_conflict ls.(logstate.prev) es ents = W64 0 ∨
     (uint.Z ls.(logstate.committed) < uint.Z (plog_find_conflict ls.(logstate.prev) es ents))%Z) →
    (* this file: the current term: [r.step(m)], by role *)
    m.(raftpb.Message.Term') = s.(nstate.term) →
    (* a follower's vote tally is empty ([padopt_leader] clears it, and
       [nstate_wf] does not say so); see the combining file *)
    (s.(nstate.role) = role.Follower → s.(nstate.votes) = ∅) →
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
    intros Hty Hto Hterm Hfnz Hfid Hcfg Hwf Hpwf Hnw Hnorm Hconf Hteq Hvotes.
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
    assert (Hsfw : s.(nstate.stepfn) = step_func_of s.(nstate.role)) by exact Hwf.
    wp_start_folded as "@". wp_start_unfold. wp_auto.
    wp_apply wp_traceReceiveMessage. try wp_auto.
    assert (bool_decide (m.(raftpb.Message.Term') = W64 0) = false) as Hz
      by by apply bool_decide_eq_false_2.
    rewrite Hz. rewrite bool_decide_eq_false_2; last done. wp_auto.
    wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
    assert (bool_decide (uint.Z s.(nstate.term) <
                         uint.Z m.(raftpb.Message.Term')) = false) as Hb
      by (apply bool_decide_eq_false_2; rewrite Hteq; lia).
    rewrite Hb Htf. wp_auto.
    wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
    assert (bool_decide (uint.Z m.(raftpb.Message.Term') <
                         uint.Z s.(nstate.term)) = false) as Hb2
      by (apply bool_decide_eq_false_2; rewrite Hteq; lia).
    rewrite Hb2 Htf. wp_auto.
    rewrite Hn0. wp_auto.
    rewrite Hn20. wp_auto.
    rewrite Hn22. wp_auto.
    rewrite Hn17. wp_auto.
    rewrite Hn5. wp_auto.
    wp_load_step.
    destruct s.(nstate.role) eqn:Hrole.
    - (* Follower: [stepFollower]'s arm, with [r.lead = m.From] *)
      assert (s.(nstate.stepfn) = functions raft.stepFollower []) as Hsf
        by (rewrite Hsfw ?Hrole //).
      rewrite Hsf.
      pose proof (Hvotes eq_refl) as Hvs.
      wp_apply (P.wp_stepFollower _ _ _ _ _ ents (zero_val _) [] with "[$Hphys Hcap]").
      { do 2 right; left. exact Hty. }
      { intros Hc. exfalso. rewrite Hty3 in Hc. revert Hc. w32_ne. }
      { intros _. split_and!; [exact Hpwf|exact Hnw|exact Hnorm|exact Hconf]. }
      { intros Hc. exfalso. rewrite Hty3 in Hc. revert Hc. w32_ne. }
      { iSplitR; [step_no_snap|]. iIntros "_". iFrame "Hents Hcap". }
      iIntros (err s1 dropped) "(Hphys & %Hres & Herrn)".
      apply follower_step_result_app in Hres as [-> Hres]; last exact Hty.
      iDestruct "Herrn" as %Herrn. rewrite Herrn. wp_auto.
      iApply ("HΦ" $! interface.nil s1). iFrame "Hphys". iPureIntro.
      split; first (eapply nstate_wf_handle_app; [|exact Hres]; exact Hwf).
      split; last done.
      exists [abs_msg mtype.App m ents]. split; first recv_elem.
      apply (step_handle_app cfg id _ _ m ents s1
               (adopt_follower s m.(raftpb.Message.From') Hrole Hvs)).
      + exact Hto.
      + exact Hteq.
      + simpl. rewrite Hrole. done.
      + exact Hconf.
      + exact Hres.
      + exact Hfid.
    - (* Candidate: [becomeFollower(r.Term, m.From)], then the handler *)
      assert (s.(nstate.stepfn) = functions raft.stepCandidate []) as Hsf
        by (rewrite Hsfw ?Hrole //).
      rewrite Hsf.
      wp_apply (P.wp_stepCandidate _ _ _ _ _ ents (zero_val _) [] with "[$Hphys Hcap]").
      { do 2 right; left. exact Hty. }
      { intros _. exact Hteq. }
      { exact Hrole. }
      { exact Hcfg. }
      { intros _. split_and!; [exact Hpwf|exact Hnw|exact Hnorm|exact Hconf]. }
      { intros Hc. exfalso. rewrite Hty3 in Hc. revert Hc. w32_ne. }
      { iSplitR; [step_no_snap|]. iIntros "_". iFrame "Hents Hcap". }
      iIntros (err s1 dropped) "(Hphys & %Hres & Herrn)".
      apply candidate_step_result_app in Hres as [-> [pvs Hres]]; last exact Hty.
      iDestruct "Herrn" as %Herrn. rewrite Herrn. wp_auto.
      iApply ("HΦ" $! interface.nil s1). iFrame "Hphys". iPureIntro.
      split; first (eapply nstate_wf_handle_app; [|exact Hres]; done).
      split; last done.
      exists [abs_msg mtype.App m ents]. split; first recv_elem.
      apply (step_handle_app cfg id _ _ m ents s1
               (adopt_candidate s m.(raftpb.Message.From') pvs)).
      + exact Hto.
      + exact Hteq.
      + simpl. rewrite Hrole. done.
      + exact Hconf.
      + exact Hres.
      + exact Hfid.
    - (* Leader: [stepLeader] has no arm for it; nothing changes *)
      assert (s.(nstate.stepfn) = functions raft.stepLeader []) as Hsf
        by (rewrite Hsfw ?Hrole //).
      rewrite Hsf.
      iAssert (⌜ m.(raftpb.Message.Type') = MsgHeartbeatResp ⌝ -∗
               m.(raftpb.Message.Context') ↦*□ ([] : list w8))%I as "Hctx0".
      { iIntros "%Hc". exfalso. revert Hc. rewrite Hty /MsgHeartbeatResp. w32_ne. }
      iAssert (⌜ m.(raftpb.Message.Type') = MsgProp ⌝ -∗
               m.(raftpb.Message.Entries') ↦* ([] : list raftpb.Entry.t))%I as "Hents0".
      { iIntros "%Hc". exfalso. revert Hc. rewrite Hty /MsgProp. w32_ne. }
      wp_apply (P.wp_stepLeader _ _ _ _ _ [] with "[$Hphys $Hctx0 $Hents0]")
        as (err s' dropped) "(Hphys & %Hres & Herrn & _)".
      { do 5 right; left. exact Hty. }
      { exact Hrole. }
      { exact Hcfg. }
      { rewrite Hty /MsgAppResp. intros Hc. exfalso. revert Hc. w32_ne. }
      { rewrite Hty /MsgAppResp /MsgHeartbeatResp.
        intros [Hc|[Hc _]]; exfalso; revert Hc; w32_ne. }
      { rewrite Hty /MsgProp. intros Hc. exfalso. revert Hc. w32_ne. }
      apply leader_step_result_app_hb in Hres as [-> ->]; last (left; exact Hty).
      iDestruct "Herrn" as %Herrn. rewrite Herrn. wp_auto.
      iApply ("HΦ" $! interface.nil s). iFrame "Hphys".
      iPureIntro. split; first exact Hwf. split; last done.
      exists []. split; last apply step_refl.
      recv_elem.
  Qed.

End branches.

End StepMsgAppEq.
