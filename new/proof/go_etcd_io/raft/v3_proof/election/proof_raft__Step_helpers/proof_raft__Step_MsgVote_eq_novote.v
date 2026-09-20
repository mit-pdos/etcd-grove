(** One case of [Step]'s [MsgVote] branch with [m.Term ≤ r.Term], in its own
    file so that it checks in parallel with the others -- see
    [proof_raft__Step_MsgVote_le.v], which combines them, and
    [notes/decisions.md] (2026-09-17; 2026-09-18 for why this directory
    exists).  Proof structure, not specification:
    no [Module Type], no [Parameter]; only [proof_raft__Step_MsgVote_le.v]
    may [Require] this file. *)
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__Step.

Module StepMsgVoteEqNovote (P : STEP_POSTULATES).
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

  (** [Step]'s [MsgVote] decision has exactly two tails -- grant the vote or
      decline it -- and the code reaches each of them by several routes
      through the [canVote] computation (already voted for this candidate; not
      voted and no leader; voted for somebody else; a leader is known).  The
      program point they start at is in the middle of [Step]'s body, so there
      is no closed expression to state a lemma about; they are tactics
      instead.  [Ltac] does not late-bind identifiers in [constr] positions,
      so every hypothesis a script uses is an argument -- the same convention
      as [wp_log] in [inv_raft_phys.v]. *)

  (** Grant the vote in the *current* term: log, [send] the response, and
      record [r.Vote := m.From].  [can] is the model-level [can_vote]. *)
  Local Ltac vote_grant_tail r_ id_ s_ m_ lok_eq ty_eq to_eq can :=
    wp_auto;
    wp_apply wp_slice_literal; iSplitR; [done|]; iIntros "% [? _]";
    wp_auto; rewrite lok_eq;
    wp_apply (wp_Logger__logf with "Hlogger");
      [solve_log_method|];
    wp_apply P.wp_voteRespMsgType; [done|];
    iAssert (own_raft_phys cfg r_ id_ s_)
      with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]"
      as "Hphys";
      [iApply (own_raft_phys_intro with
          "Hlogger Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc"); done|];
    wp_apply (P.wp_raft__send with "[$Hphys]") as "Hphys";
      [done|left; exists mtype.VoteResp; split_and!;
            [by right|apply mtype_of_MsgVoteResp|done|w32_ne|done]|];
    (* [wp_hidden]: an [iNamed] on a goal holding the whole body is ~12s *)
    wp_hidden (iNamedSuffix "Hphys" "2");
    rewrite ty_eq /MsgVote bool_decide_eq_true_2 //;
    wp_auto;
    iApply ("HΦ" $! interface.nil
      (send_msgs (s_ <| nstate.vote := m_.(raftpb.Message.From') |>)
         [msg.mk mtype.VoteResp id_ m_.(raftpb.Message.From')
            m_.(raftpb.Message.Term') false]));
    (* [own_raft_phys_intro] does not apply here: its [s] is fixed by [Htrk2],
       whose state is [send]'s [abs_msg] form of the message, and
       [iApply] does not unify that with the [msg.mk] form in the goal.  Naming
       the hypotheses to frame (instead of [iFrame "∗#%"]) is 2s against 17s. *)
    iSplitL "Hr2 Htrk2 Hlog2 Hmsgs2 Hmsgs_cap2 HmsgsAA2 HmsgsAA_cap2 Hmisc2";
      [rewrite /own_raft_phys /send_msgs /=;
       iExists _, _, _, _;
       iEval (simpl) in "Htrk2";
       iFrame "Hr2 Htrk2 Hlog2 Hmsgs2 Hmsgs_cap2 HmsgsAA2 HmsgsAA_cap2 Hmisc2 Hlogger2";
       simpl in *; iPureIntro; first [done | (split_and!; done)]|];
    iPureIntro; split; [|done];
    exists [abs_msg mtype.Vote m_];
    split; [recv_elem|];
    replace m_.(raftpb.Message.Term') with s_.(nstate.term) by congruence;
    apply (step_grant_vote cfg id_ (abs_msg mtype.Vote m_) s_);
      [done|exact to_eq|(rewrite /abs_msg /=; congruence)|exact can].

  (** Decline: log, then [send] a rejection carrying [r.Term].  Always legal,
      so there is no side condition beyond the message being a [MsgVote]
      addressed to us.  [term_eq] is [own_raft_phys]'s [r.Term = s.term]. *)
  Local Ltac vote_reject_tail r_ id_ s_ m_ lok_eq to_eq term_eq :=
    wp_auto;
    wp_apply wp_slice_literal; iSplitR; [done|]; iIntros "% [? _]";
    wp_auto; rewrite lok_eq;
    wp_apply (wp_Logger__logf with "Hlogger");
      [solve_log_method|];
    wp_apply P.wp_voteRespMsgType; [done|];
    rewrite term_eq;
    iAssert (own_raft_phys cfg r_ id_ s_)
      with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]"
      as "Hphys";
      [iApply (own_raft_phys_intro with
          "Hlogger Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc"); done|];
    (* The response carries [s.term], so [send]'s [m.Term ≠ 0] premise is the
       incoming message's, transported along [term_eq].  The [simpl] is not
       optional: the premise is stated about the *message literal*, so the
       goal is [{| ... |}.(Message.Term') ≠ W64 0] and [congruence] -- unlike
       [done]/[assumption] -- does not see through the projection. *)
    wp_apply (P.wp_raft__send with "[$Hphys]") as "Hphys";
      [done|left; exists mtype.VoteResp; split_and!;
            [by right|apply mtype_of_MsgVoteResp|(simpl; congruence)|w32_ne|done]|];
    iApply ("HΦ" $! interface.nil _); iFrame "Hphys";
    iPureIntro; split; [|done];
    exists [abs_msg mtype.Vote m_];
    split; [recv_elem|];
    apply (step_reject_vote cfg id_ (abs_msg mtype.Vote m_) s_);
      [done|exact to_eq].

  (** [MsgVote]: step down if the term is higher, then grant or decline.

      The thing to know before editing this proof is that **[canVote]'s
      Go-level shape decides how many [bool_decide]s each arm owes**.  The Go
      expression is

          (Vote == m.From) || (Vote == None && lead == None)
                           || (m.Type == MsgPreVote && m.Term > r.Term)

      and Goose compiles [||]/[&&] to short-circuiting [If]s
      ([new/golang/defn/postlang.v]), so the number of comparisons [wp_auto]
      actually evaluates differs per arm:

      - [Vote = m.From]: one ([true], done).
      - [Vote = None], [lead = None]: three (the second disjunct is [true]).
      - [Vote = None], [lead ≠ None]: **four** -- the second disjunct is
        [false], so the third is evaluated and its [MsgPreVote] test is live.
      - [Vote ≠ None], [Vote ≠ m.From]: **three** -- [A] and [B] are [false],
        then the [MsgPreVote] test again.

      The two four/three-comparison arms are the two that decline, and an
      earlier version of this script left their [MsgPreVote] [bool_decide]
      undischarged.  [wp_auto] then stopped in front of it, and the failure
      surfaced fifteen lines later as [iApply: cannot apply] at the
      [lastEntryID] call.  So each arm does its own [bool_decide] bookkeeping
      and only then calls the shared tail; the tails themselves
      ([vote_grant_tail] / [vote_reject_tail]) assume the program is sitting
      right after [lastEntryID] with [canVote] already decided. *)
  (** [MsgVote] with [m.Term = r.Term] and [r.Vote = None]: grant if no leader
      is known and the candidate's log is up to date, else decline. *)
  Lemma wp_Step_MsgVote_eq_novote r id s (m : raftpb.Message.t) :
    m.(raftpb.Message.Type') = MsgVote →
    m.(raftpb.Message.To') = id →
    m.(raftpb.Message.Term') ≠ W64 0 →
    (* [send] stamps the sender's id into [From], and node ids are nonzero *)
    m.(raftpb.Message.From') ≠ W64 0 →
    (* this file: same term, and this node has not voted in it *)
    m.(raftpb.Message.Term') = s.(nstate.term) →
    s.(nstate.vote) = W64 0 →
    {{{ is_pkg_init raft ∗
        "Hphys" ∷ own_raft_phys cfg r id s ∗
        (* the message's [Context] is readable and is not the leader-transfer
           marker: leader transfer is out of scope *)
        "#Hctx" ∷ (∃ ctx, m.(raftpb.Message.Context') ↦*□ ctx ∗
                          ⌜ ctx ≠ campaignTransfer ⌝)
    }}}
      r @! (go.PointerType raft.raft) @! "Step" #m
    {{{ (err : error.t) s', RET #err;
        "Hphys" ∷ own_raft_phys cfg r id s' ∗
        (* [recv] is whatever this branch consumed -- nothing, or the incoming
           message once or twice.  Naming its elements rather than the list
           lets [wp_raft__Step] discharge the [is_message] side of
           [own_raft_ghost_step] from the single fact it holds about [m]. *)
        "%Hrefines" ∷ ⌜ ∃ recv,
            (∀ m', m' ∈ recv → m' = abs_msg mtype.Vote m) ∧
            step cfg id s recv s' ⌝ ∗
        "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.
  Proof.
    intros Hty Hto Hterm Hfnz Heq0 Hv00.
    wp_start_folded as "@". iNamed "Hphys". wp_start_unfold. wp_auto.
    assert (Hle : ¬ (uint.Z rv.(raft.raft.Term') < uint.Z m.(raftpb.Message.Term')))
      by (rewrite Hterm0 Heq0; lia).
    assert (Hnlt : ¬ (uint.Z m.(raftpb.Message.Term') < uint.Z rv.(raft.raft.Term')))
      by (rewrite Hterm0 Heq0; lia).
    assert (Hv0 : rv.(raft.raft.Vote') = W64 0) by (rewrite Hvote; exact Hv00).
    wp_apply (wp_traceReceiveMessage with "[$Hmisc]") as "Hmisc".
    (* [m.Term ≠ 0], so the first arm of the term preamble is skipped. *)
    assert (bool_decide (m.(raftpb.Message.Term') = W64 0) = false) as Hz
    by by apply bool_decide_eq_false_2.
    rewrite Hz. rewrite bool_decide_eq_false_2; last done. wp_auto.
      assert (bool_decide (uint.Z rv.(raft.raft.Term') <
                           uint.Z m.(raftpb.Message.Term')) = false) as Hb
        by by apply bool_decide_eq_false_2.
      rewrite Hb. rewrite bool_decide_eq_false_2; last done. wp_auto.
        assert (bool_decide (uint.Z m.(raftpb.Message.Term') <
                             uint.Z rv.(raft.raft.Term')) = false) as Hb2
          by by apply bool_decide_eq_false_2.
        rewrite Hb2. rewrite bool_decide_eq_false_2; last done. wp_auto.
        assert (Hrt : rv.(raft.raft.Term') = m.(raftpb.Message.Term')) by word.
        (* the type switch: not MsgHup / MsgStorageAppendResp /
           MsgStorageApplyResp, not MsgPreVote, but MsgVote *)
        rewrite Hty /MsgVote bool_decide_eq_false_2; last w32_ne. wp_auto.
        (* [canVote] is the model's [can_vote]: the Go expression's third
           disjunct needs [MsgPreVote] and is dead here. *)
          rewrite Hv0 bool_decide_eq_false_2; last congruence. wp_auto.
          rewrite Hv0 bool_decide_eq_true_2 //. wp_auto.
          destruct (decide (rv.(raft.raft.lead') = W64 0)) as [Hl0|Hl0].
          -- (* and recognises no leader: [canVote] *)
             rewrite Hl0 bool_decide_eq_true_2 //. wp_auto.
             assert (Hcan : can_vote s m.(raftpb.Message.From'))
               by (right; split; congruence).
             wp_apply (wp_raftLog__lastEntryID with "[$Hlog]")
               as "%lastID2 Hlog".
             wp_apply (wp_raftLog__isUpToDate with "[$Hlog]") as "%ok2 Hlog".
             destruct ok2.
             ++ vote_grant_tail r id s m Hlok Hty Hto Hcan.
             ++ vote_reject_tail r id s m Hlok Hto Hterm0.
          -- (* but a leader is known, so the vote is declined.  [canVote]'s
                  second disjunct is now false, so the program goes on to
                  evaluate the third -- which needs [MsgPreVote].  This arm
                  therefore discharges one more [bool_decide] than the
                  [lead = None] one above, which short-circuited to [true]. *)
             rewrite bool_decide_eq_false_2; last congruence. wp_auto.
             rewrite (bool_decide_eq_false_2
                        (m.(raftpb.Message.Type') = W32 17));
               last (rewrite Hty /MsgVote; w32_ne).
             wp_auto.
             (* No [as]: it would run [wp_auto], which here steps straight
                through the [canVote && isUpToDate] test (both operands are
                literals once [canVote] is [false]) and on into the rejection
                branch -- leaving [vote_reject_tail]'s own leading [wp_auto]
                with nothing to do.  The arms that call [isUpToDate] block on
                its [bool] result instead, so they can use [as]. *)
             wp_apply (wp_raftLog__lastEntryID with "[$Hlog]").
             iIntros "%lastID2 Hlog".
             vote_reject_tail r id s m Hlok Hto Hterm0.
  Qed.

End branches.

End StepMsgVoteEqNovote.
