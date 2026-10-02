(** One branch of [Step]'s proof: [MsgProp], a local proposal.

    This is **proof structure, not specification**: [Step] has exactly one
    spec, in [spec_raft__Step.v], and this module has no [Module Type] and no
    [Parameter].  Nothing but [proof_raft__Step.v], or another file in this
    directory, may [Require] it; see [notes/decisions.md] (2026-09-17, and
    2026-09-18 for why the helpers moved out of the top-level directory). *)
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__Step.

Module StepMsgProp (P : STEP_POSTULATES).
Import P.

Section branches.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).

Implicit Type γ : raft_election_names.
Implicit Type s : nstate.t.

  (** See [proof_raft__Step_MsgVoteResp.v]: the load of [r.step] sits in
      function position, so it is bound by hand. *)
  Local Ltac wp_load_step :=
    wp_bind (![raft.stepFunc] _)%E;
    iApply (wp_raft_load_step with "Hphys"); iIntros "!> Hphys".

  (** [Step]'s tail after [r.step(r, m)]: [if err != nil { return err }],
      then [return nil].  Either way the function returns [err]. *)
  Local Ltac finish_err err :=
    destruct err as [?|]; wp_auto.

  (** [∀ m', m' ∈ recv → m' = a] for [recv] [[]] or [[a]]; as in
      [proof_raft__Step_MsgVoteResp.v], not [set_solver]. *)
  Local Ltac recv_elem :=
    intros ? Hin;
    rewrite ?elem_of_app ?list_elem_of_singleton ?elem_of_nil in Hin;
    naive_solver.

  (** A dropped proposal: the state is unchanged ([step_refl]) and [err] is
      [ErrProposalDropped]'s value. *)
  Local Ltac finish_drop :=
    iSplitR; first (iPureIntro; done);
    iSplitR; first (iPureIntro; exists []; split; [recv_elem | apply step_refl]);
    iRight; iSimpl in "Herrn"; iFrame "Herrn".

  (** [proposed] ([spec_stepLeader.v]) is [step_propose]'s state: the log
      grows by the batch stamped at the leader's term and the indices after
      the last one, and the self-acknowledgement at the new last index is
      queued.  (Checked 2026-10-02: the physical definition and the rule
      agree; nothing needed changing.) *)
  Local Lemma to_pstate_proposed id s ents :
    to_pstate (proposed id s ents) =
    psend_msgs
      (pappend (to_pstate s) (imap (stamp s.(nstate.term) (plast_index (to_pstate s))) ents))
      [pself_ack id
         (pappend (to_pstate s) (imap (stamp s.(nstate.term) (plast_index (to_pstate s))) ents))].
  Proof.
    set (ps1 := pappend (to_pstate s)
                  (imap (stamp s.(nstate.term) (plast_index (to_pstate s))) ents)).
    rewrite /proposed to_pstate_send_msgs.
    set (s1 := s <| nstate.logst := log_append s.(nstate.logst)
                 (imap (stamp s.(nstate.term) (log_last s.(nstate.logst))) ents) |>).
    assert (Hs1 : to_pstate s1 = ps1).
    { rewrite /ps1 plast_index_to_pstate /s1 /to_pstate /pappend /log_append /=.
      rewrite app_assoc //. }
    rewrite Hs1. f_equal. f_equal.
    rewrite /self_ack /pself_ack -Hs1 plast_index_to_pstate //.
  Qed.

  (** [MsgProp]: a local message ([Term = 0]), so the term preamble is
      skipped and the type switch's default arm runs [r.step(r, m)]:

      - [stepFollower] forwards it to the leader ([step_prop_forward]), or,
        with no leader known, drops it ([step_refl], [ErrProposalDropped]).
        [send] holds the entries read-only, so the batch is made persistent
        first;
      - [stepCandidate] drops it;
      - [stepLeader] appends it ([step_propose]) and broadcasts
        ([step_send_apps]), or drops it when [appendEntry] refuses the
        batch.

      [recv] is the proposal itself when it is forwarded, and nothing
      otherwise.  [lead_ok] ([protocol.v], from [own_raft_ghost]) is what
      makes the follower's forwarding [send] not self-addressed. *)
  Lemma wp_Step_MsgProp r id s (m : raftpb.Message.t) (ents : list raftpb.Entry.t) :
    m.(raftpb.Message.Type') = MsgProp →
    m.(raftpb.Message.Term') = W64 0 →
    m.(raftpb.Message.From') = W64 0 →
    ents ≠ [] →
    Forall (λ e, e.(raftpb.Entry.Type') = EntryNormal) ents →
    (Z.of_nat (length ents) < 2^61)%Z →
    (s.(nstate.role) ≠ role.Leader → s.(nstate.lead) ≠ id) →
    id ∈ cfg →
    nstate_wf s →
    {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s ∗
        "Hents" ∷ m.(raftpb.Message.Entries') ↦* ents ∗
        "Hcap" ∷ own_slice_cap raftpb.Entry.t m.(raftpb.Message.Entries') (DfracOwn 1) }}}
      r @! (go.PointerType raft.raft) @! "Step" #m
    {{{ (err : error.t) s', RET #err;
        "Hphys" ∷ own_raft_phys cfg r id s' ∗
        "%Hwf'" ∷ ⌜ nstate_wf s' ⌝ ∗
        "%Hrefines" ∷ ⌜ ∃ recv,
            (∀ m', m' ∈ recv → m' = abs_msg mtype.Propose m ents) ∧
            step cfg id (to_pstate s) recv (to_pstate s') ⌝ ∗
        "Herr" ∷ (⌜ err = interface.nil ⌝ ∨ global_addr raft.ErrProposalDropped ↦□ err) }}}.
  Proof.
    intros Hty Hterm Hfrom Hne Hnorm Hlen Hlok Hcfg Hwf.
    assert (Hsfw : s.(nstate.stepfn) = step_func_of s.(nstate.role)) by exact Hwf.
    assert (Hty2 : m.(raftpb.Message.Type') = W32 2) by (rewrite Hty //).
    (* the type switch's tests: MsgHup(0), MsgStorageAppendResp(20),
       MsgStorageApplyResp(22), MsgPreVote(17)||MsgVote(5) *)
    assert (Hn0 : bool_decide (m.(raftpb.Message.Type') = W32 0) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty2; w32_ne).
    assert (Hn20 : bool_decide (m.(raftpb.Message.Type') = W32 20) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty2; w32_ne).
    assert (Hn22 : bool_decide (m.(raftpb.Message.Type') = W32 22) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty2; w32_ne).
    assert (Hn17 : bool_decide (m.(raftpb.Message.Type') = W32 17) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty2; w32_ne).
    assert (Hn5 : bool_decide (m.(raftpb.Message.Type') = W32 5) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty2; w32_ne).
    (* the other types' premises of the [stepX] specs are vacuous *)
    assert (Hnot : ∀ t : w32, t ≠ W32 2 → m.(raftpb.Message.Type') ≠ t).
    { intros t Ht Hc. apply Ht. rewrite -Hc Hty2 //. }
    wp_start_folded as "@". wp_start_unfold. wp_auto.
    wp_apply wp_traceReceiveMessage. try wp_auto.
    (* [m.Term = 0]: a local message, the term preamble is skipped *)
    rewrite Hterm !bool_decide_eq_true_2 //.
    wp_auto.
    (* the type switch: none of its cases, so the default arm [r.step(m)] *)
    rewrite Hn0. wp_auto.
    rewrite Hn20. wp_auto.
    rewrite Hn22. wp_auto.
    rewrite Hn17. wp_auto.
    rewrite Hn5. wp_auto.
    wp_load_step.
    destruct s.(nstate.role) eqn:Hrole.
    - (* Follower: forward to the leader, or drop.  [send] wants the
         entries read-only. *)
      assert (s.(nstate.stepfn) = functions raft.stepFollower []) as Hsf
        by (rewrite Hsfw ?Hrole //).
      rewrite Hsf.
      iMod (own_slice_persist with "Hents") as "#Hents".
      wp_apply (P.wp_stepFollower _ _ _ _ _ ents with "[$Hphys Hcap]").
      { right; left. exact Hty. }
      { intros _. split_and!; [exact Hfrom | exact Hterm | apply Hlok; rewrite Hrole; done]. }
      { intros Hc. exfalso. by apply (Hnot MsgApp); [w32_ne|]. }
      { intros Hc. exfalso. by apply (Hnot MsgHeartbeat); [w32_ne|]. }
      { iIntros "_". iFrame "#∗". }
      iIntros (err s1 dropped) "(Hphys & %Hres & Herrn)".
      (* [case_decide] takes the outermost [decide] (notes/gotchas.md) *)
      revert Hres. rewrite /follower_step_result.
      case_decide as Hc; first (exfalso; revert Hc; apply Hnot; w32_ne).
      case_decide as Hc'; last (intros; exfalso; by apply Hc').
      case_decide as Hl0; intros [-> ->].
      + (* no leader known: dropped *)
        finish_err err; (iApply ("HΦ" $! _ s); iFrame "Hphys"; finish_drop).
      + (* forwarded: [step_prop_forward] *)
        iDestruct "Herrn" as %->.
        wp_auto.
        iApply ("HΦ" $! interface.nil _). iFrame "Hphys".
        iSplitR; first (iPureIntro; exact Hwf).
        iSplitR; last (iLeft; by iPureIntro).
        iPureIntro.
        exists [abs_msg mtype.Propose m ents]. split.
        { recv_elem. }
        rewrite to_pstate_send_msgs.
        apply (step_prop_forward cfg id (to_pstate s) (abs_msg mtype.Propose m ents)).
        * done.
        * exact Hrole.
        * exact Hl0.
    - (* Candidate: drop *)
      assert (s.(nstate.stepfn) = functions raft.stepCandidate []) as Hsf
        by (rewrite Hsfw ?Hrole //).
      rewrite Hsf.
      wp_apply (P.wp_stepCandidate _ _ _ _ _ ents with "[$Hphys]").
      { right; left. exact Hty. }
      { intros Hc. exfalso.
        destruct Hc as [Hc|[Hc|Hc]]; revert Hc; apply Hnot; w32_ne. }
      { exact Hrole. }
      { exact Hcfg. }
      { intros Hc. exfalso. by apply (Hnot MsgApp); [w32_ne|]. }
      { intros Hc. exfalso. by apply (Hnot MsgHeartbeat); [w32_ne|]. }
      { iIntros "%Hc". exfalso. by apply (Hnot MsgApp); [w32_ne|]. }
      iIntros (err s1 dropped) "(Hphys & %Hres & Herrn)".
      revert Hres. rewrite /candidate_step_result.
      case_decide as Hc; first (exfalso; revert Hc; apply Hnot; w32_ne).
      case_decide as Hc'; last (intros; exfalso; by apply Hc').
      intros [-> ->].
      finish_err err; (iApply ("HΦ" $! _ s); iFrame "Hphys"; finish_drop).
    - (* Leader: append and broadcast, or drop *)
      assert (s.(nstate.stepfn) = functions raft.stepLeader []) as Hsf
        by (rewrite Hsfw ?Hrole //).
      rewrite Hsf.
      iAssert (⌜ m.(raftpb.Message.Type') = MsgHeartbeatResp ⌝ -∗
               m.(raftpb.Message.Context') ↦*□ ([] : list w8))%I as "Hctx0".
      { iIntros "%Hc". exfalso. by apply (Hnot MsgHeartbeatResp); [w32_ne|]. }
      iAssert (⌜ m.(raftpb.Message.Type') = MsgProp ⌝ -∗
               m.(raftpb.Message.Entries') ↦* ents)%I with "[Hents]" as "Hents".
      { iIntros "_". iFrame "Hents". }
      wp_apply (P.wp_stepLeader _ _ _ _ _ ents with "[$Hphys $Hctx0 $Hents]")
        as (err s' dropped) "(Hphys & %Hres & Herrn & _)".
      { right; right; right; right; left. exact Hty. }
      { exact Hrole. }
      { exact Hcfg. }
      { intros Hc. exfalso. by apply (Hnot MsgAppResp); [w32_ne|]. }
      { intros [Hc|[Hc _]]; exfalso; revert Hc; apply Hnot; w32_ne. }
      { intros _. split_and!; [exact Hne | exact Hnorm | exact Hlen]. }
      rewrite /leader_step_result decide_True in Hres; last exact Hty.
      rewrite /leader_propose_result in Hres.
      destruct dropped; cbv beta iota in Hres.
      + (* [appendEntry] refused the batch *)
        subst s'.
        finish_err err; (iApply ("HΦ" $! _ s); iFrame "Hphys"; finish_drop).
      + destruct Hres as (ms & pvs & -> & Hms & Hpvs).
        iDestruct "Herrn" as %->.
        wp_auto.
        (* the appended log does not wrap: [own_raftLog]'s [Hnowrap] at the
           new state *)
        iDestruct (own_raft_phys_log_same with "Hphys") as "[Hlog Hback]".
        iDestruct (own_raftLog_nowrap with "Hlog") as "[%Hnw Hlog]".
        iDestruct ("Hback" with "Hlog") as "Hphys".
        iApply ("HΦ" $! interface.nil _). iFrame "Hphys".
        iSplitR; first (iPureIntro; exact Hwf).
        iSplitR; last (iLeft; by iPureIntro).
        iPureIntro.
        exists ([] ++ []). split; first recv_elem.
        rewrite to_pstate_prvals; last first.
        { intros _. rewrite Hpvs //. }
        rewrite to_pstate_send_msgs to_pstate_proposed.
        rewrite /repl_sends to_pstate_proposed in Hms.
        eapply step_trans.
        { apply step_propose.
          - exact Hrole.
          - exact Hnorm.
          - (* [Hnw] is about the state after the append *)
            simpl in Hnw. rewrite length_app length_imap in Hnw.
            rewrite /plog_last_index_Z /= length_app. lia. }
        apply step_send_apps; [exact Hrole|exact Hms].
  Qed.

End branches.

End StepMsgProp.
