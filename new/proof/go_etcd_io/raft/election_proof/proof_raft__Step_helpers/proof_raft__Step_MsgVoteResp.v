(** One branch of [Step]'s proof, in its own file so that the three branches
    check in parallel under [make -j] -- each is a few minutes of [wp_auto]
    over the same 100k-node body, and in one file they ran back to back.

    This is **proof structure, not specification**: [Step] has exactly one
    spec, in [spec_raft__Step.v], and this module has no [Module Type] and no
    [Parameter].  Nothing but [proof_raft__Step.v], or another file in this
    directory, may [Require] it; see [notes/decisions.md] (2026-09-17, and
    2026-09-18 for why the helpers moved out of the top-level directory). *)
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__Step.

Module StepMsgVoteResp (P : STEP_POSTULATES).
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

  (** The load of [r.step] in [r.step(r, m)].  Not [wp_raft_field]: the load
      sits in the *function* position of an application, and [wp_apply]
      does not find it there ("iApply: cannot apply", 2026-09-24); binding
      it by hand with [wp_bind] and then applying the lemma works. *)
  Local Ltac wp_load_step :=
    wp_bind (![raft.stepFunc] _)%E;
    iApply (wp_raft_load_step with "Hphys"); iIntros "!> Hphys".

  (** [MsgVoteResp]: the term preamble, then [r.step(m)].

      The one branch where all three [stepX] can run, so it is also the one
      that needs the [r.step] field pinned to the role: [wp_raft_load_step]
      loads [s.stepfn], and [nstate_wf] says it is [step_func_of s.role] --
      without that there is nothing to apply at [r.step(m)].  Three
      term cases, and the third splits three ways:

      - [m.Term > r.Term]: a [VoteResp] is not [from_leader], so the
        preamble runs [becomeFollower(m.Term, None)] rather than adopting a
        leader.  The role is [Follower] afterwards, so [r.step] is
        [stepFollower], which has no [MsgVoteResp] arm.  One
        [step_higher_term].
      - [m.Term < r.Term]: with [checkQuorum] and [preVote] both off, and a
        [MsgVoteResp] being neither [MsgPreVote] nor [MsgStorageAppendResp],
        every arm of the chain is skipped but the last, which only logs.
        Then [return nil].  [step_refl], with [recv = []] -- the message is
        dropped, which the model always permits.
      - [m.Term = r.Term]: straight to the type switch's default arm.
        [stepFollower] and [stepLeader] only read, so again [step_refl];
        [stepCandidate] records the vote and may win or lose in the same
        call, which is [step_record_then_win] / [step_record_then_lose] /
        [step_record_vote] on its [won]/[lost] flags. *)
  Lemma wp_Step_MsgVoteResp r id s (m : raftpb.Message.t) :
    m.(raftpb.Message.Type') = MsgVoteResp →
    m.(raftpb.Message.To') = id →
    m.(raftpb.Message.Term') ≠ W64 0 →
    (* [stepCandidate] needs it; [Step] is the outermost caller, so it enters
       the development at [wp_raft__Step_body] -- see spec_raft__Step.v *)
    id ∈ cfg →
    (* [r.step] matches the role and nothing is on loan *)
    nstate_wf s →
    {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s }}}
      r @! (go.PointerType raft.raft) @! "Step" #m
    {{{ (err : error.t) s', RET #err;
        "Hphys" ∷ own_raft_phys cfg r id s' ∗
        "%Hwf'" ∷ ⌜ nstate_wf s' ⌝ ∗
        "%Hrefines" ∷ ⌜ ∃ recv,
            (∀ m', m' ∈ recv → m' = abs_msg mtype.VoteResp m) ∧
            step cfg id (to_pstate s) recv (to_pstate s') ⌝ ∗
        "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.
  Proof.
    intros Hty Hto Hterm Hcfg Hwf.
    pose proof Hwf as [Hsfw Hlent].
    assert (Hty6 : m.(raftpb.Message.Type') = W32 6) by (rewrite Hty //).
    (* Hoist every type test this branch meets, as named facts.  Rewriting
       [bool_decide (Type = k)] inline hits whichever occurrence comes first,
       and Goose nests the tests
       ([bool_decide (true = bool_decide (Type = 17))]), so inline rewriting
       peels the wrong layer.  Named facts + [rewrite] are what the MsgVote
       proof does. *)
    assert (Hn17 : bool_decide (m.(raftpb.Message.Type') = W32 17) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty6; w32_ne).
    assert (Hn18 : bool_decide (m.(raftpb.Message.Type') = W32 18) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty6; w32_ne).
    assert (Hn5 : bool_decide (m.(raftpb.Message.Type') = W32 5) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty6; w32_ne).
    assert (Hn3 : bool_decide (m.(raftpb.Message.Type') = W32 3) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty6; w32_ne).
    assert (Hn8 : bool_decide (m.(raftpb.Message.Type') = W32 8) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty6; w32_ne).
    assert (Hn7 : bool_decide (m.(raftpb.Message.Type') = W32 7) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty6; w32_ne).
    (* Goose's short-circuit [||]/[&&] leave [bool_decide (true = <inner>)]
       wrappers; once [<inner>] is [false] this collapses them. *)
    assert (Htf : bool_decide (true = false) = false) by done.
    (* the type switch's four tests: MsgHup(0), MsgStorageAppendResp(20),
       MsgStorageApplyResp(22), MsgPreVote(17)||MsgVote(5) *)
    assert (Hn0 : bool_decide (m.(raftpb.Message.Type') = W32 0) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty6; w32_ne).
    assert (Hn20 : bool_decide (m.(raftpb.Message.Type') = W32 20) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty6; w32_ne).
    assert (Hn22 : bool_decide (m.(raftpb.Message.Type') = W32 22) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty6; w32_ne).
    wp_start_folded as "@". wp_start_unfold. wp_auto.
    wp_apply wp_traceReceiveMessage. try wp_auto.
    assert (bool_decide (m.(raftpb.Message.Term') = W64 0) = false) as Hz
      by by apply bool_decide_eq_false_2.
    rewrite Hz. rewrite bool_decide_eq_false_2; last done. wp_auto.
    wp_raft_field.
    destruct (decide (uint.Z s.(nstate.term) < uint.Z m.(raftpb.Message.Term')))
      as [Hgt|Hle].
    - (* m.Term > r.Term: step down, then dispatch to stepFollower *)
      assert (bool_decide (uint.Z s.(nstate.term) <
                           uint.Z m.(raftpb.Message.Term')) = true) as Hb
        by by apply bool_decide_eq_true_2.
      rewrite Hb. rewrite bool_decide_eq_true_2 //. wp_auto.
      (* (Type == MsgVote) || (Type == MsgPreVote): both false *)
      rewrite Hn5. wp_auto.
      (* the lease-check block: not MsgPreVote *)
      rewrite Hn17. wp_auto.
      (* second occurrence, this time wrapped: [true = bool_decide (…17)] *)
      rewrite Hn17 Htf. wp_auto.
      (* not (MsgPreVoteResp && !Reject) *)
      rewrite Hn18. wp_auto.
      (* the "received a message with higher term" Infof *)
      wp_raft_log.
      (* a MsgVoteResp is not from a leader: not MsgApp/Heartbeat/Snap *)
      rewrite Hn3. wp_auto.
      (* not MsgHeartbeat, not MsgSnap either, so the else arm runs
         becomeFollower(m.Term, None) rather than adopting a leader *)
      rewrite Hn8. wp_auto.
      rewrite Hn7. wp_auto.
      wp_apply (P.wp_raft__becomeFollower _ _ _ _ _ _ Hlent with "[$Hphys]")
        as "Hphys".
      (* the model step: a VoteResp is not from_leader, so no leader is
         adopted and the new lead is 0 *)
      assert (step cfg id (to_pstate s) [abs_msg mtype.VoteResp m]
                (to_pstate (become_follower s m.(raftpb.Message.Term') (W64 0)))) as Hsd.
      { rewrite to_pstate_become_follower.
        replace (W64 0) with
          (if from_leader (abs_msg mtype.VoteResp m).(msg.ty)
           then (abs_msg mtype.VoteResp m).(msg.from) else W64 0) by done.
        replace m.(raftpb.Message.Term') with
          (abs_msg mtype.VoteResp m).(msg.term) by done.
        apply step_higher_term.
        - rewrite /abs_msg /=. exact Hgt.
        - rewrite /abs_msg /=. exact Hto. }
      (* the type switch: none of its four cases matches a MsgVoteResp, so
         control reaches the default arm r.step(m) *)
      rewrite Hn0. wp_auto.
      rewrite Hn20. wp_auto.
      rewrite Hn22. wp_auto.
      rewrite Hn17. wp_auto.
      rewrite Hn5. wp_auto.
      (* the default arm, [r.step(m)].  The step-down made the role
         [Follower], so the loaded [stepfn] is [stepFollower]. *)
      wp_load_step.
      assert ((become_follower s m.(raftpb.Message.Term') (W64 0)).(nstate.stepfn)
              = functions raft.stepFollower []) as Hsf by done.
      rewrite Hsf.
      wp_apply (P.wp_stepFollower_MsgVoteResp with "[$Hphys]") as (err) "[Hphys %Herrn]".
      { done. }
      (* [stepFollower] returned [nil], so the error check falls through to
         the trailing [return nil]. *)
      rewrite Herrn. wp_auto.
      iApply ("HΦ" $! interface.nil
                (become_follower s m.(raftpb.Message.Term') (W64 0))).
      iFrame "Hphys". iPureIntro.
      split; first exact (nstate_wf_become_follower _ _ _ Hlent).
      split; last done.
      exists [abs_msg mtype.VoteResp m]. split; last exact Hsd.
      recv_elem.
    - (* m.Term ≤ r.Term *)
      assert (bool_decide (uint.Z s.(nstate.term) <
                           uint.Z m.(raftpb.Message.Term')) = false) as Hb
        by by apply bool_decide_eq_false_2.
      rewrite Hb Htf. wp_auto.
      wp_raft_field.
      destruct (decide (uint.Z m.(raftpb.Message.Term') <
                        uint.Z s.(nstate.term))) as [Hlt|Hnlt].
      + (* m.Term < r.Term.  [checkQuorum] and [preVote] are both off and a
           [MsgVoteResp] is neither [MsgPreVote] nor [MsgStorageAppendResp],
           so every arm is skipped but the last, which only logs; then
           [return nil].  Nothing changed: [step_refl]. *)
        assert (bool_decide (uint.Z m.(raftpb.Message.Term') <
                             uint.Z s.(nstate.term)) = true) as Hb2
          by by apply bool_decide_eq_true_2.
        rewrite Hb2. rewrite bool_decide_eq_true_2 //. wp_auto.
        wp_raft_field.
        wp_raft_field.
        rewrite Hn17. wp_auto.
        rewrite Hn20. wp_auto.
        wp_raft_log.
        iApply ("HΦ" $! interface.nil s). iFrame "Hphys".
        iPureIntro. split; first exact Hwf. split; last done.
        exists []. split; last apply step_refl.
        recv_elem.
      + (* m.Term = r.Term: the preamble does nothing and control reaches the
           type switch, whose default arm is [r.step(m)]. *)
        assert (bool_decide (uint.Z m.(raftpb.Message.Term') <
                             uint.Z s.(nstate.term)) = false) as Hb2
          by by apply bool_decide_eq_false_2.
        rewrite Hb2 Htf. wp_auto.
        assert (m.(raftpb.Message.Term') = s.(nstate.term)) as Hteq
          by word.
        rewrite Hn0. wp_auto.
        rewrite Hn20. wp_auto.
        rewrite Hn22. wp_auto.
        rewrite Hn17. wp_auto.
        rewrite Hn5. wp_auto.
        (* the default arm, [r.step(m)].  Unlike the higher-term branch the
           role is untouched, so all three [stepX] are possible. *)
        wp_load_step.
        destruct s.(nstate.role) eqn:Hrole.
        * (* Follower: [stepFollower] has no [MsgVoteResp] arm. *)
          assert (s.(nstate.stepfn) = functions raft.stepFollower []) as Hsf
            by (rewrite Hsfw ?Hrole //).
          rewrite Hsf.
          wp_apply (P.wp_stepFollower_MsgVoteResp with "[$Hphys]")
            as (err) "[Hphys %Herrn]".
          { done. }
          rewrite Herrn. wp_auto.
          iApply ("HΦ" $! interface.nil s). iFrame "Hphys".
          iPureIntro. split; first exact Hwf. split; last done.
          exists []. split; last apply step_refl.
          recv_elem.
        * (* Candidate: [stepCandidate] records the vote and may win or lose
             in the same call. *)
          assert (s.(nstate.stepfn) = functions raft.stepCandidate []) as Hsf
            by (rewrite Hsfw ?Hrole //).
          rewrite Hsf.
          wp_apply (P.wp_stepCandidate_MsgVoteResp with "[$Hphys]")
            as (err s') "(Hphys & %Hres & %Herrn)".
          { done. }
          { exact Hto. }
          { exact Hteq. }
          { exact Hrole. }
          { exact Hcfg. }
          { exact Hlent. }
          rewrite Herrn. wp_auto.
          destruct Hres as (won & lost & ms & Hms & Hwon & Hlost & ->).
          iApply ("HΦ" $! interface.nil _). iFrame "Hphys".
          iPureIntro. split; first by apply nstate_wf_vote_resp_result.
          split; last done.
          exists [abs_msg mtype.VoteResp m]. split.
          { recv_elem. }
          rewrite to_pstate_vote_resp_result /pvote_resp_result.
          destruct won.
          { eapply (step_record_then_win cfg id (to_pstate s) (abs_msg mtype.VoteResp m) ms).
            - done.
            - rewrite /abs_msg /=. exact Hto.
            - rewrite /abs_msg /=. exact Hteq.
            - exact Hrole.
            - simpl. exact Hms.
            - simpl. by apply Hwon. }
          destruct lost.
          { eapply (step_record_then_lose cfg id (to_pstate s) (abs_msg mtype.VoteResp m)).
            - done.
            - rewrite /abs_msg /=. exact Hto.
            - rewrite /abs_msg /=. exact Hteq.
            - exact Hrole.
            - simpl. by apply Hlost. }
          apply step_record_vote.
          { done. }
          { rewrite /abs_msg /=. exact Hto. }
          { rewrite /abs_msg /=. exact Hteq. }
          { exact Hrole. }
        * (* Leader: [stepLeader]'s [MsgVoteResp] arm only reads. *)
          assert (s.(nstate.stepfn) = functions raft.stepLeader []) as Hsf
            by (rewrite Hsfw ?Hrole //).
          rewrite Hsf.
          wp_apply (P.wp_stepLeader_MsgVoteResp with "[$Hphys]")
            as (err) "[Hphys %Herrn]".
          { done. }
          { exact Hlent. }
          rewrite Herrn. wp_auto.
          iApply ("HΦ" $! interface.nil s). iFrame "Hphys".
          iPureIntro. split; first exact Hwf. split; last done.
          exists []. split; last apply step_refl.
          recv_elem.
  Qed.

End branches.

End StepMsgVoteResp.
