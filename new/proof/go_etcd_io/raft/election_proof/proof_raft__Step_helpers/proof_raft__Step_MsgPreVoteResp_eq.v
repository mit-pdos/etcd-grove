(** One term case of [Step]'s [MsgPreVoteResp] branch (2026-10-04): the
    incoming term is the node's own.  In its own file so that it checks in
    parallel with the others; [proof_raft__Step_MsgPreVoteResp.v] combines
    them.  Proof structure, not specification: no [Module Type], no
    [Parameter]; only files in this directory may [Require] it. *)
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_prevote_lemmas.

Module StepMsgPreVoteRespEq (P : STEP_POSTULATES).
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

  (** [MsgPreVoteResp] at [m.Term = r.Term]: the preamble does nothing and
      the type switch's default arm runs [r.step(m)].  Only a pre-candidate
      acts on it ([stepCandidate] with [myVoteRespType = MsgPreVoteResp]:
      the tally, then [campaign(campaignElection)] on a win,
      [becomeFollower] on a loss); everyone else ignores it.  Nothing is
      received by the protocol: [step_refl], [step_abandon] or
      [step_campaign] ([step_prevote_resp_result]). *)
  Lemma wp_Step_MsgPreVoteResp_eq r id s (m : raftpb.Message.t)
      (ents : list raftpb.Entry.t) :
    m.(raftpb.Message.Type') = MsgPreVoteResp →
    m.(raftpb.Message.To') = id →
    m.(raftpb.Message.Term') ≠ W64 0 →
    (* this file: the same term *)
    m.(raftpb.Message.Term') = s.(nstate.term) →
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
    intros Hty Hto Hterm Hteq Hnw Hcfg Hwf.
    assert (Hsfw : s.(nstate.stepfn) = step_func_of s.(nstate.role)) by exact Hwf.
    assert (Hty18 : m.(raftpb.Message.Type') = W32 18) by (rewrite Hty //).
    assert (Hn17 : bool_decide (m.(raftpb.Message.Type') = W32 17) = false) by ne_ty Hty.
    assert (Hn5 : bool_decide (m.(raftpb.Message.Type') = W32 5) = false) by ne_ty Hty.
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
                         uint.Z m.(raftpb.Message.Term')) = false) as Hb
      by (apply bool_decide_eq_false_2; rewrite Hteq; lia).
    rewrite Hb Htf. wp_auto.
    wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
    assert (bool_decide (uint.Z m.(raftpb.Message.Term') <
                         uint.Z s.(nstate.term)) = false) as Hb2
      by (apply bool_decide_eq_false_2; rewrite Hteq; lia).
    rewrite Hb2 Htf. wp_auto.
    (* the type switch: none of its four cases, so [r.step(m)] *)
    rewrite Hn0. wp_auto.
    rewrite Hn20. wp_auto.
    rewrite Hn22. wp_auto.
    rewrite Hn17. wp_auto.
    rewrite Hn5. wp_auto.
    wp_load_step.
    destruct s.(nstate.role) eqn:Hrole.
    - (* Follower: no arm *)
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
    - (* Candidate: [myVoteRespType] is [MsgVoteResp]; a stale pre-vote
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
    - (* Leader: no arm *)
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
    - (* PreCandidate: the pre-vote tally *)
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

End StepMsgPreVoteRespEq.
