(** One term case of [Step]'s [MsgSnap] branch (the current term: [r.step(m)]
    by role), in its own file so that it checks in parallel with the
    others; [proof_raft__Step_MsgSnap.v] combines them.  A leader is
    excluded by a premise (the dispatch refutes a second leader of the
    term, [is_leader_unique]).  Proof structure, not specification: no
    [Module Type], no [Parameter]; only files in this directory may
    [Require] it. *)
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_repl_lemmas.

Module StepMsgSnapEq (P : STEP_POSTULATES).
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

  Lemma wp_Step_MsgSnap_eq r id s (m : raftpb.Message.t)
      (sv : raftpb.Snapshot.t) (voters : list w64) :
    m.(raftpb.Message.Type') = MsgSnap →
    m.(raftpb.Message.To') = id →
    m.(raftpb.Message.Term') ≠ W64 0 →
    m.(raftpb.Message.From') ≠ W64 0 →
    m.(raftpb.Message.From') ≠ id →
    id ∈ cfg →
    nstate_wf s →
    snap_scope cfg sv voters →
    (* this file: the current term *)
    m.(raftpb.Message.Term') = s.(nstate.term) →
    (* not a leader: the sender leads this term ([is_leader_unique]) *)
    s.(nstate.role) ≠ prole.Leader →
    (* a follower's vote tally is empty ([follower_votes_ok]) *)
    (s.(nstate.role) = prole.Follower → s.(nstate.votes) = ∅) →
    {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s ∗
        "#Hsv" ∷ m.(raftpb.Message.Snapshot') ↦□ sv ∗
        "#Hvs" ∷ sv.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.ConfState')
                   .(raftpb.ConfState.Voters') ↦*□ voters }}}
      r @! (go.PointerType raft.raft) @! "Step" #m
    {{{ (err : error.t) s', RET #err;
        "Hphys" ∷ own_raft_phys cfg r id s' ∗
        "%Hwf'" ∷ ⌜ nstate_wf s' ⌝ ∗
        "%Hrefines" ∷ ⌜ ∃ recv,
            (∀ m', m' ∈ recv → m' = abs_snap m sv voters) ∧
            step cfg id (to_pstate s) recv (to_pstate s') ⌝ ∗
        "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.
  Proof.
    intros Hty Hto Hterm Hfnz Hfid Hcfg Hwf Hscope Hteq Hnl Hvotes.
    assert (Hty7 : m.(raftpb.Message.Type') = W32 7) by (rewrite Hty //).
    assert (Hn17 : bool_decide (m.(raftpb.Message.Type') = W32 17) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty7; w32_ne).
    assert (Hn5 : bool_decide (m.(raftpb.Message.Type') = W32 5) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty7; w32_ne).
    assert (Hn0 : bool_decide (m.(raftpb.Message.Type') = W32 0) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty7; w32_ne).
    assert (Hn20 : bool_decide (m.(raftpb.Message.Type') = W32 20) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty7; w32_ne).
    assert (Hn22 : bool_decide (m.(raftpb.Message.Type') = W32 22) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty7; w32_ne).
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
      wp_apply (P.wp_stepFollower _ _ _ _ _ [] sv voters with "[$Hphys]").
      { do 5 right; left. exact Hty. }
      { intros Hc. exfalso. rewrite Hty7 in Hc. revert Hc. w32_ne. }
      { intros Hc. exfalso. rewrite Hty7 in Hc. revert Hc. w32_ne. }
      { intros Hc. exfalso. rewrite Hty7 in Hc. revert Hc. w32_ne. }
      { iSplitR.
        - iIntros "_". iFrame "Hsv Hvs". iPureIntro.
          split_and!; [exact Hscope|exact Hrole|exact Hvs|exact Hcfg].
        - iIntros "%Hc". exfalso. rewrite Hty7 in Hc. destruct Hc as [Hc|Hc]; revert Hc; w32_ne. }
      iIntros (err s1 dropped) "(Hphys & %Hres & Herrn)".
      apply follower_step_result_snap in Hres as [-> Hres]; last exact Hty.
      iDestruct "Herrn" as %Herrn. rewrite Herrn. wp_auto.
      iApply ("HΦ" $! interface.nil s1). iFrame "Hphys". iPureIntro.
      split; first (eapply nstate_wf_handle_snap; [|exact Hres]; exact Hwf).
      split; last done.
      exists [abs_snap m sv voters]. split; first recv_elem.
      apply (step_handle_snap cfg id _ _ m sv voters s1
               (adopt_follower s m.(raftpb.Message.From') Hrole Hvs)).
      + exact Hto.
      + exact Hteq.
      + simpl. rewrite Hrole. done.
      + exact Hfid.
      + exact Hscope.
      + exact Hcfg.
      + exact Hres.
    - (* Candidate: [becomeFollower(r.Term, m.From)], then [handleSnapshot] *)
      assert (s.(nstate.stepfn) = functions raft.stepCandidate []) as Hsf
        by (rewrite Hsfw ?Hrole //).
      rewrite Hsf.
      wp_apply (P.wp_stepCandidate _ _ _ _ _ [] sv voters with "[$Hphys]").
      { do 5 right; left. exact Hty. }
      { intros _. exact Hteq. }
      { by left. }
      { exact Hcfg. }
      { intros Hc. exfalso. rewrite Hty7 in Hc. revert Hc. w32_ne. }
      { intros Hc. exfalso. rewrite Hty7 in Hc. revert Hc. w32_ne. }
      { intros _ Hc. exfalso. revert Hc. rewrite Hty. w32_ne. }
      { iSplitR.
        - iIntros "_". iFrame "Hsv Hvs". iPureIntro. exact Hscope.
        - iIntros "%Hc". exfalso. rewrite Hty7 in Hc. revert Hc. w32_ne. }
      iIntros (err s1 dropped) "(Hphys & %Hres & Herrn)".
      apply candidate_step_result_snap in Hres as [-> [pvs Hres]]; last exact Hty.
      iDestruct "Herrn" as %Herrn. rewrite Herrn. wp_auto.
      iApply ("HΦ" $! interface.nil s1). iFrame "Hphys". iPureIntro.
      split; first (eapply nstate_wf_handle_snap; [|exact Hres]; done).
      split; last done.
      exists [abs_snap m sv voters]. split; first recv_elem.
      apply (step_handle_snap cfg id _ _ m sv voters s1
               (adopt_candidate s m.(raftpb.Message.From') pvs)).
      + exact Hto.
      + exact Hteq.
      + simpl. rewrite Hrole. done.
      + exact Hfid.
      + exact Hscope.
      + exact Hcfg.
      + exact Hres.
    - (* Leader: excluded *)
      exfalso. by apply Hnl.
    - (* PreCandidate (2026-10-04), as a candidate:: [becomeFollower(r.Term, m.From)], then [handleSnapshot] *)
      assert (s.(nstate.stepfn) = functions raft.stepCandidate []) as Hsf
        by (rewrite Hsfw ?Hrole //).
      rewrite Hsf.
      wp_apply (P.wp_stepCandidate _ _ _ _ _ [] sv voters with "[$Hphys]").
      { do 5 right; left. exact Hty. }
      { intros _. exact Hteq. }
      { by right. }
      { exact Hcfg. }
      { intros Hc. exfalso. rewrite Hty7 in Hc. revert Hc. w32_ne. }
      { intros Hc. exfalso. rewrite Hty7 in Hc. revert Hc. w32_ne. }
      { intros _ Hc. exfalso. revert Hc. rewrite Hty. w32_ne. }
      { iSplitR.
        - iIntros "_". iFrame "Hsv Hvs". iPureIntro. exact Hscope.
        - iIntros "%Hc". exfalso. rewrite Hty7 in Hc. revert Hc. w32_ne. }
      iIntros (err s1 dropped) "(Hphys & %Hres & Herrn)".
      apply candidate_step_result_snap in Hres as [-> [pvs Hres]]; last exact Hty.
      iDestruct "Herrn" as %Herrn. rewrite Herrn. wp_auto.
      iApply ("HΦ" $! interface.nil s1). iFrame "Hphys". iPureIntro.
      split; first (eapply nstate_wf_handle_snap; [|exact Hres]; done).
      split; last done.
      exists [abs_snap m sv voters]. split; first recv_elem.
      apply (step_handle_snap cfg id _ _ m sv voters s1
               (adopt_candidate s m.(raftpb.Message.From') pvs)).
      + exact Hto.
      + exact Hteq.
      + simpl. rewrite Hrole. done.
      + exact Hfid.
      + exact Hscope.
      + exact Hcfg.
      + exact Hres.
  Qed.

End branches.

End StepMsgSnapEq.
