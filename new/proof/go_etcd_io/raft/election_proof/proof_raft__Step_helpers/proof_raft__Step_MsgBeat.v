(** [Step]'s [MsgBeat] branch, in its own file so that it checks in
    parallel with the others.  Proof structure, not specification: no
    [Module Type], no [Parameter]; only [proof_raft__Step.v] may [Require]
    this file. *)
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_resp_lemmas.

Module StepMsgBeat (P : STEP_POSTULATES).
Import P.

Section branches.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).

Implicit Type s : nstate.t.

  Local Ltac wp_load_step :=
    wp_bind (![raft.stepFunc] _)%E;
    iApply (wp_raft_load_step with "Hphys"); iIntros "!> Hphys".

  Local Ltac ne_ty Hty :=
    apply bool_decide_eq_false_2; rewrite Hty; w32_ne.

  (** [MsgBeat] is local ([m.Term = 0]: [tickHeartbeat] builds it), so the
      term preamble is skipped; it is none of the type switch's four cases,
      so [r.step(m)] runs.  [stepFollower] and [stepCandidate] have no arm
      for it ([step_refl]); [stepLeader] runs [bcastHeartbeat], whose
      heartbeats are [step_beat]'s ([leader_beat_step]). *)
  Lemma wp_Step_MsgBeat r id s (m : raftpb.Message.t) :
    m.(raftpb.Message.Type') = MsgBeat →
    m.(raftpb.Message.Term') = W64 0 →
    id ∈ cfg →
    nstate_wf s →
    {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s }}}
      r @! (go.PointerType raft.raft) @! "Step" #m
    {{{ (err : error.t) s', RET #err;
        "Hphys" ∷ own_raft_phys cfg r id s' ∗
        "%Hwf'" ∷ ⌜ nstate_wf s' ⌝ ∗
        "%Hrefines" ∷ ⌜ step cfg id (to_pstate s) [] (to_pstate s') ⌝ ∗
        "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.
  Proof.
    intros Hty Hterm Hcfg Hwf.
    assert (Hsfw : s.(nstate.stepfn) = step_func_of s.(nstate.role)) by exact Hwf.
    assert (Hty3 : m.(raftpb.Message.Type') = MsgBeat ∨
                   m.(raftpb.Message.Type') = MsgAppResp ∨
                   m.(raftpb.Message.Type') = MsgHeartbeatResp) by auto.
    assert (Hn17 : bool_decide (m.(raftpb.Message.Type') = W32 17) = false) by ne_ty Hty.
    assert (Hn5 : bool_decide (m.(raftpb.Message.Type') = W32 5) = false) by ne_ty Hty.
    assert (Hn0 : bool_decide (m.(raftpb.Message.Type') = W32 0) = false) by ne_ty Hty.
    assert (Hn20 : bool_decide (m.(raftpb.Message.Type') = W32 20) = false) by ne_ty Hty.
    assert (Hn22 : bool_decide (m.(raftpb.Message.Type') = W32 22) = false) by ne_ty Hty.
    wp_start_folded as "@". wp_start_unfold. wp_auto.
    wp_apply wp_traceReceiveMessage. try wp_auto.
    (* [m.Term = 0] (a local message), so the term preamble is skipped. *)
    rewrite Hterm !bool_decide_eq_true_2 //.
    wp_auto.
    (* the type switch: none of its four cases, so [r.step(m)] *)
    rewrite Hn0. wp_auto.
    rewrite Hn20. wp_auto.
    rewrite Hn22. wp_auto.
    rewrite Hn17. wp_auto.
    rewrite Hn5. wp_auto.
    wp_load_step.
    destruct s.(nstate.role) eqn:Hrole.
    - (* Follower: no [MsgBeat] arm *)
      assert (s.(nstate.stepfn) = functions raft.stepFollower []) as Hsf
        by (rewrite Hsfw ?Hrole //).
      rewrite Hsf.
      wp_apply (P.wp_stepFollower _ _ _ _ _ [] with "[$Hphys]").
      { right; right; right; right. exact Hty3. }
      { intros Hc. exfalso. rewrite Hty in Hc. revert Hc. w32_ne. }
      { intros Hc. exfalso. rewrite Hty in Hc. revert Hc. w32_ne. }
      { intros Hc. exfalso. rewrite Hty in Hc. revert Hc. w32_ne. }
      { iIntros "%Hc". exfalso. rewrite Hty in Hc.
        destruct Hc as [Hc|Hc]; revert Hc; w32_ne. }
      iIntros (err s1 dropped) "(Hphys & %Hres & Herrn)".
      destruct (follower_step_result_noop _ _ _ _ _ _ Hty3 Hres) as [-> ->]. iDestruct "Herrn" as %Herrn.
      rewrite Herrn. wp_auto.
      iApply ("HΦ" $! interface.nil s). iFrame "Hphys".
      iPureIntro. split; first exact Hwf. split; last done.
      apply step_refl.
    - (* Candidate: no [MsgBeat] arm either *)
      assert (s.(nstate.stepfn) = functions raft.stepCandidate []) as Hsf
        by (rewrite Hsfw ?Hrole //).
      rewrite Hsf.
      wp_apply (P.wp_stepCandidate _ _ _ _ _ [] with "[$Hphys]").
      { right; right; right; right. exact Hty3. }
      { intros Hc. exfalso. rewrite Hty in Hc.
        destruct Hc as [Hc|[Hc|Hc]]; revert Hc; w32_ne. }
      { exact Hrole. }
      { exact Hcfg. }
      { intros Hc. exfalso. rewrite Hty in Hc. revert Hc. w32_ne. }
      { intros Hc. exfalso. rewrite Hty in Hc. revert Hc. w32_ne. }
      { iIntros "%Hc". exfalso. rewrite Hty in Hc. revert Hc. w32_ne. }
      iIntros (err s1 dropped) "(Hphys & %Hres & Herrn)".
      destruct (candidate_step_result_noop cfg _ _ _ _ _ _ Hty3 Hres) as [-> ->]. iDestruct "Herrn" as %Herrn.
      rewrite Herrn. wp_auto.
      iApply ("HΦ" $! interface.nil s). iFrame "Hphys".
      iPureIntro. split; first exact Hwf. split; last done.
      apply step_refl.
    - (* Leader: [bcastHeartbeat] *)
      assert (s.(nstate.stepfn) = functions raft.stepLeader []) as Hsf
        by (rewrite Hsfw ?Hrole //).
      rewrite Hsf.
      iAssert (⌜ m.(raftpb.Message.Type') = MsgHeartbeatResp ⌝ -∗
               m.(raftpb.Message.Context') ↦*□ ([] : list w8))%I as "Hctx0".
      { iIntros "%Hc". exfalso. revert Hc. rewrite Hty. w32_ne. }
      iAssert (⌜ m.(raftpb.Message.Type') = MsgProp ⌝ -∗
               m.(raftpb.Message.Entries') ↦* ([] : list raftpb.Entry.t))%I as "Hents0".
      { iIntros "%Hc". exfalso. revert Hc. rewrite Hty. w32_ne. }
      wp_apply (P.wp_stepLeader _ _ _ _ _ [] with "[$Hphys $Hctx0 $Hents0]")
        as (err s' dropped) "(Hphys & %Hres & Herrn & _)".
      { right; left. exact Hty. }
      { exact Hrole. }
      { exact Hcfg. }
      { intros Hc. exfalso. revert Hc. rewrite Hty. w32_ne. }
      { intros [Hc|[Hc _]]; exfalso; revert Hc; rewrite Hty; w32_ne. }
      { intros Hc. exfalso. revert Hc. rewrite Hty. w32_ne. }
      destruct (leader_beat_step cfg id s m [] dropped s' Hrole Hty Hwf Hres)
        as (-> & Hwf' & Hstep).
      iDestruct "Herrn" as %Herrn.
      rewrite Herrn. wp_auto.
      iApply ("HΦ" $! interface.nil s'). iFrame "Hphys".
      iPureIntro. split; first exact Hwf'. split; last done.
      exact Hstep.
  Qed.

End branches.

End StepMsgBeat.
