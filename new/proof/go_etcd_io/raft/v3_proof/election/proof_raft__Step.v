(** The three per-message-type lemmas are **proof structure, not
    specification**.  [Step] is one Go function and therefore has exactly one
    spec, in [spec_raft__Step.v]; giving each branch its own [Module Type]
    would put four Hoare triples for [r.Step] in four files, which is the
    thing this layout exists to prevent.  They live here, sealed by the
    ascription, so no other file can state or depend on them. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__Step.

Module StepProof (P : STEP_POSTULATES) : STEP.

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

  (** [MsgHup] is a local message ([m.Term = 0]), so [Step]'s term preamble
      is skipped entirely and it goes straight to [hup].

      Like the other two branch lemmas this is ghost-free: it establishes the
      [step] witness as a pure fact, and [wp_raft__Step] below turns the three
      of them into the single [own_raft_ghost_step] of the whole development. *)
  Lemma wp_Step_MsgHup r id s (m : raftpb.Message.t) :
    m.(raftpb.Message.Type') = MsgHup →
    m.(raftpb.Message.Term') = W64 0 →
    (* an election increments the term; [send] panics if that wraps to zero *)
    uint.Z s.(nstate.term) + 1 < 2 ^ 64 →
    {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s }}}
      r @! (go.PointerType raft.raft) @! "Step" #m
    {{{ (err : error.t) s', RET #err;
        "Hphys" ∷ own_raft_phys cfg r id s' ∗
        "%Hrefines" ∷ ⌜ step cfg id s [] s' ⌝ ∗
        "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.
  Proof.
    intros Hty Hterm Hnowrap.
    (* Take the precondition apart *before* the body is unfolded into the
       goal: every [iDestruct] is linear in the goal size, and the translated
       [Step] body is ~500KB.  See [wp_start_unfold]. *)
    wp_start_folded as "@".
    iNamed "Hphys".
    wp_start_unfold.
    wp_auto.
    wp_apply (wp_traceReceiveMessage with "[$Hmisc]") as "Hmisc".
    (* [m.Term = 0] (a local message), so the term preamble is skipped. *)
    rewrite Hterm !bool_decide_eq_true_2 //.
    wp_auto.
    (* the type switch selects the [MsgHup] case *)
    rewrite Hty /MsgHup bool_decide_eq_true_2 //.
    wp_auto.
    (* no pre-vote, so this is a plain [hup(campaignElection)] *)
    rewrite HnoPreVote. wp_auto.
    (* re-seal the physical ownership for [hup] *)
    (* re-seal with [own_raft_phys_intro] rather than [iFrame "∗#%"], which
       costs ~17s against the unfolded predicate *)
    iAssert (own_raft_phys cfg r id s)
    with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]" as "Hphys".
    { iApply (own_raft_phys_intro with
          "Hlogger Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc"); done. }
    wp_apply (P.wp_raft__hup with "[$Hphys]") as "%s' (Hphys & %Hstep)".
    { done. }
    { exact Hnowrap. }
    iApply ("HΦ" $! interface.nil s'). by iFrame.
  Qed.

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
    wp_apply (P.wp_raft__send_vote with "[$Hphys]") as "Hphys";
      [done|by right|apply mtype_of_MsgVoteResp|done|w32_ne|];
    (* [wp_hidden]: an [iNamed] on a goal holding the whole body is ~12s *)
    wp_hidden (iNamedSuffix "Hphys" "2");
    rewrite ty_eq /MsgVote bool_decide_eq_true_2 //;
    wp_auto;
    iApply ("HΦ" $! interface.nil
      (send_msgs (s_ <| nstate.vote := m_.(raftpb.Message.From') |>)
         [msg.mk mtype.VoteResp id_ m_.(raftpb.Message.From')
            m_.(raftpb.Message.Term') false]));
    (* [own_raft_phys_intro] does not apply here: its [s] is fixed by [Htrk2],
       whose state is [send_vote]'s [abs_msg] form of the message, and
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
    wp_apply (P.wp_raft__send_vote with "[$Hphys]") as "Hphys";
      [done|by right|apply mtype_of_MsgVoteResp|(simpl; congruence)|w32_ne|];
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
  Lemma wp_Step_MsgVote r id s (m : raftpb.Message.t) :
    m.(raftpb.Message.Type') = MsgVote →
    m.(raftpb.Message.To') = id →
    m.(raftpb.Message.Term') ≠ W64 0 →
    (* [send] stamps the sender's id into [From], and node ids are nonzero *)
    m.(raftpb.Message.From') ≠ W64 0 →
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
    intros Hty Hto Hterm Hfnz.
    wp_start_folded as "@". iNamed "Hphys". wp_start_unfold. wp_auto.
    wp_apply (wp_traceReceiveMessage with "[$Hmisc]") as "Hmisc".
    (* [m.Term ≠ 0], so the first arm of the term preamble is skipped. *)
    assert (bool_decide (m.(raftpb.Message.Term') = W64 0) = false) as Hz
    by by apply bool_decide_eq_false_2.
    rewrite Hz. rewrite bool_decide_eq_false_2; last done. wp_auto.
    destruct (decide (uint.Z rv.(raft.raft.Term') < uint.Z m.(raftpb.Message.Term')))
    as [Hgt|Hle].
    - (* [m.Term > r.Term]: step down to follower first, then answer. *)
    assert (bool_decide (uint.Z rv.(raft.raft.Term') <
                         uint.Z m.(raftpb.Message.Term')) = true) as Hb
      by by apply bool_decide_eq_true_2.
    rewrite Hb. rewrite bool_decide_eq_true_2 //. wp_auto.
    rewrite Hty /MsgVote bool_decide_eq_true_2 //. wp_auto.
    (* [force] is false (not a leader transfer) and [inLease] is false (no
       check-quorum), so the lease check does not drop the message. *)
    iDestruct "Hctx" as (ctx) "[Hctx_sl %Hctx_ne]".
    wp_apply wp_string_to_bytes as "%ct_sl [ct_sl ct_cap]".
    wp_apply (wp_Equal _ _ DfracDiscarded (DfracOwn 1) ctx ("CampaignTransfer"%go)
                with "[$Hctx_sl $ct_sl]") as "[_ ct_sl2]".
    rewrite HnoCheckQuorum. wp_auto.
    assert (bool_decide (ctx = "CampaignTransfer"%go) = false) as Hnf
      by by apply bool_decide_eq_false_2.
    rewrite Hnf. wp_auto.
    (* neither MsgPreVote nor MsgPreVoteResp, so we fall through to the
       step-down *)
    assert (bool_decide (m.(raftpb.Message.Type') = W32 17) = false) as Hpv
      by (apply bool_decide_eq_false_2; rewrite Hty /MsgVote; w32_ne).
    rewrite Hpv. rewrite bool_decide_eq_false_2; last done. wp_auto.
    assert (bool_decide (m.(raftpb.Message.Type') = W32 18) = false) as Hpvr
      by (apply bool_decide_eq_false_2; rewrite Hty /MsgVote; w32_ne).
    rewrite Hpvr. wp_auto.
    wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [Hlog_sl _]".
    wp_auto. rewrite Hlok.
    wp_apply (wp_Logger__logf with "Hlogger").
    { solve_log_method. }
    (* a [MsgVote] is not from a leader, so no leader is adopted *)
    rewrite Hty /MsgVote bool_decide_eq_false_2; last w32_ne. wp_auto.
    rewrite Hty /MsgVote bool_decide_eq_false_2; last w32_ne. wp_auto.
    rewrite Hty /MsgVote bool_decide_eq_false_2; last w32_ne. wp_auto.
    iAssert (own_raft_phys cfg r id s)
      with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]" as "Hphys".
    { iApply (own_raft_phys_intro with
          "Hlogger Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc"); done. }
    wp_apply (P.wp_raft__becomeFollower with "[$Hphys]") as "Hphys".
    (* the corresponding protocol step, recorded as a pure fact rather than
       taken on the ghost state: this lemma is ghost-free. *)
    assert (step cfg id s [abs_msg mtype.Vote m]
              (become_follower s m.(raftpb.Message.Term') (W64 0))) as Hstepdown.
    { replace (W64 0) with
        (if from_leader (abs_msg mtype.Vote m).(msg.ty)
         then (abs_msg mtype.Vote m).(msg.from) else W64 0) by done.
      replace m.(raftpb.Message.Term') with (abs_msg mtype.Vote m).(msg.term)
        by done.
      apply step_higher_term.
      - rewrite /abs_msg /= -Hterm0. exact Hgt.
      - rewrite /abs_msg /=. exact Hto. }
    wp_hidden (iNamedSuffix "Hphys" "1").
    (* the type switch: not MsgHup / MsgStorageAppendResp / MsgStorageApplyResp,
       not MsgPreVote, but MsgVote *)
    rewrite Hty /MsgVote bool_decide_eq_false_2; last w32_ne. wp_auto.
    (* Stepping down to a strictly greater term cleared both [Vote] and
       [lead], so [canVote] holds. *)
    assert (Hne : m.(raftpb.Message.Term') ≠ s.(nstate.term)).
    { rewrite -Hterm0. intros Heq. rewrite Heq in Hgt. lia. }
    rewrite /become_follower /= decide_False // in Hvote1 Hlead1.
    rewrite Hvote1 bool_decide_eq_false_2; last congruence. wp_auto.
    rewrite Hvote1 bool_decide_eq_true_2 //. wp_auto.
    rewrite Hlead1 bool_decide_eq_true_2 //. wp_auto.
    wp_apply (wp_raftLog__lastEntryID with "[$Hlog1]") as "%lastID Hlog1".
    wp_apply (wp_raftLog__isUpToDate with "[$Hlog1]") as "%uptodate Hlog1".
    destruct uptodate.
    + (* the candidate's log is up to date: grant the vote *)
      wp_auto.
      wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
      wp_auto. rewrite Hlok1.
      wp_apply (wp_Logger__logf with "Hlogger1").
      { solve_log_method. }
      wp_apply P.wp_voteRespMsgType; first done.
      (* the protocol step: grant the vote.  The [VoteResp] it sends is no
         longer a separate output -- it is the growth of the outbox, which the
         [send] below has to match. *)
      assert (step cfg id (become_follower s m.(raftpb.Message.Term') (W64 0))
                [abs_msg mtype.Vote m]
                (send_msgs ((become_follower s m.(raftpb.Message.Term') (W64 0))
                              <| nstate.vote := m.(raftpb.Message.From') |>)
                   [msg.mk mtype.VoteResp id m.(raftpb.Message.From')
                      m.(raftpb.Message.Term') false])) as Hgrant.
      { apply step_grant_vote; [done|exact Hto|done|].
        rewrite /can_vote /become_follower /=. right.
        split; [by rewrite decide_False|done]. }
      iAssert (own_raft_phys cfg r id (become_follower s m.(raftpb.Message.Term') (W64 0)))
        with "[Hr1 Htrk1 Hlog1 Hmsgs1 Hmsgs_cap1 HmsgsAA1 HmsgsAA_cap1 Hmisc1]"
        as "Hphys".
      { iApply (own_raft_phys_intro with
          "Hlogger1 Hr1 Htrk1 Hlog1 Hmsgs1 Hmsgs_cap1 HmsgsAA1 HmsgsAA_cap1 Hmisc1");
        unfold become_follower; simpl; try (rewrite decide_False; [|exact Hne]); done. }
      (* [send] the granted vote response, then record the vote. *)
      wp_apply (P.wp_raft__send_vote with "[$Hphys]") as "Hphys".
      { done. }
      { by right. }
      { apply mtype_of_MsgVoteResp. }
      { done. }
      { w32_ne. }
      wp_hidden (iNamedSuffix "Hphys" "2").
      (* [m.Type = MsgVote], so the vote is recorded: [r.Vote := m.From]. *)
      rewrite Hty /MsgVote bool_decide_eq_true_2 //. wp_auto.
      iApply ("HΦ" $! interface.nil
        (send_msgs ((become_follower s m.(raftpb.Message.Term') (W64 0))
                      <| nstate.vote := m.(raftpb.Message.From') |>)
           [msg.mk mtype.VoteResp id m.(raftpb.Message.From')
              m.(raftpb.Message.Term') false])).
      iSplitL "Hr2 Htrk2 Hlog2 Hmsgs2 Hmsgs_cap2 HmsgsAA2 HmsgsAA_cap2 Hmisc2".
      { (* see [vote_grant_tail] for why this is not [own_raft_phys_intro] *)
        rewrite /own_raft_phys /send_msgs /become_follower /=.
        iExists _, msgs1, msgsAA1, lok1.
        iEval (simpl) in "Htrk2".
        iFrame "Hr2 Htrk2 Hlog2 Hmsgs2 Hmsgs_cap2 HmsgsAA2 HmsgsAA_cap2 Hmisc2 Hlogger2".
        simpl in *. iPureIntro. first [done | (split_and!; done)]. }
      iPureIntro. split; last done.
      eexists ([abs_msg mtype.Vote m] ++ [abs_msg mtype.Vote m]).
      split.
      { recv_elem. }
      eapply step_trans; [exact Hstepdown|exact Hgrant].
    + (* the candidate's log is behind: decline, without recording a vote *)
      wp_auto.
      wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
      wp_auto. rewrite Hlok1.
      wp_apply (wp_Logger__logf with "Hlogger1").
      { solve_log_method. }
      wp_apply P.wp_voteRespMsgType; first done.
      (* [r.Term] is [m.Term] after the step-down, so the rejection carries
         the state's term -- which is what [step_reject_vote] sends. *)
      assert (Hrt : rv0.(raft.raft.Term') = m.(raftpb.Message.Term'))
        by by rewrite Hterm1.
      rewrite Hrt.
      iAssert (own_raft_phys cfg r id
                 (become_follower s m.(raftpb.Message.Term') (W64 0)))
        with "[Hr1 Htrk1 Hlog1 Hmsgs1 Hmsgs_cap1 HmsgsAA1 HmsgsAA_cap1 Hmisc1]"
        as "Hphys".
      { iApply (own_raft_phys_intro with
          "Hlogger1 Hr1 Htrk1 Hlog1 Hmsgs1 Hmsgs_cap1 HmsgsAA1 HmsgsAA_cap1 Hmisc1");
        unfold become_follower; simpl; try (rewrite decide_False; [|exact Hne]); done. }
      wp_apply (P.wp_raft__send_vote with "[$Hphys]") as "Hphys".
      { done. }
      { by right. }
      { apply mtype_of_MsgVoteResp. }
      { done. }
      { w32_ne. }
      iApply ("HΦ" $! interface.nil _). iFrame "Hphys".
      iPureIntro. split; last done.
      eexists ([abs_msg mtype.Vote m] ++ [abs_msg mtype.Vote m]).
      split.
      { recv_elem. }
      apply (step_stepdown_then_reject cfg id s (abs_msg mtype.Vote m));
        [done|exact Hto|rewrite /abs_msg /= -Hterm0; exact Hgt].
    - (* [m.Term ≤ r.Term]: no step-down. *)
      assert (bool_decide (uint.Z rv.(raft.raft.Term') <
                           uint.Z m.(raftpb.Message.Term')) = false) as Hb
        by by apply bool_decide_eq_false_2.
      rewrite Hb. rewrite bool_decide_eq_false_2; last done. wp_auto.
      destruct (decide (uint.Z m.(raftpb.Message.Term') <
                        uint.Z rv.(raft.raft.Term'))) as [Hlt|Hnlt].
      + (* [m.Term < r.Term]: a stale vote request, dropped silently. *)
        assert (bool_decide (uint.Z m.(raftpb.Message.Term') <
                             uint.Z rv.(raft.raft.Term')) = true) as Hb2
          by by apply bool_decide_eq_true_2.
        rewrite Hb2. rewrite bool_decide_eq_true_2 //. wp_auto.
        rewrite HnoCheckQuorum. wp_auto.
        rewrite HnoPreVote. wp_auto.
        (* not a MsgPreVote *)
        rewrite (bool_decide_eq_false_2 (m.(raftpb.Message.Type') = W32 17));
          last (rewrite Hty /MsgVote; w32_ne).
        wp_auto.
        (* not a MsgStorageAppendResp either, so the message is just logged *)
        rewrite (bool_decide_eq_false_2 (m.(raftpb.Message.Type') = W32 20));
          last (rewrite Hty /MsgVote; w32_ne).
        wp_auto.
        wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
        wp_auto. rewrite Hlok.
        wp_apply (wp_Logger__logf with "Hlogger").
        { solve_log_method. }
        (* nothing was sent and nothing changed: dropping is [step_refl]. *)
        iAssert (own_raft_phys cfg r id s)
          with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]"
          as "Hphys".
        { iApply (own_raft_phys_intro with
          "Hlogger Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc"); done. }
        iApply ("HΦ" $! interface.nil s). iFrame "Hphys".
        iPureIntro. split; last done. exists [].
        split; [recv_elem|apply step_drop].
      + (* [m.Term = r.Term]: answer in the current term, without stepping
           down.  [r.Term < m.Term] and [m.Term < r.Term] are both false. *)
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
        destruct (decide (rv.(raft.raft.Vote') = W64 0)) as [Hv0|Hv0].
        * (* has not voted in this term.  [m.From ≠ 0], so the first
             disjunct of [canVote] is false and the second decides it. *)
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
        * (* has already voted in this term *)
          destruct (decide (rv.(raft.raft.Vote') = m.(raftpb.Message.From')))
            as [Hv1|Hv1].
          -- (* for this very candidate, so the vote may be granted again *)
             rewrite bool_decide_eq_true_2; last congruence. wp_auto.
             assert (Hcan : can_vote s m.(raftpb.Message.From'))
               by (left; congruence).
             wp_apply (wp_raftLog__lastEntryID with "[$Hlog]")
               as "%lastID2 Hlog".
             wp_apply (wp_raftLog__isUpToDate with "[$Hlog]") as "%ok2 Hlog".
             destruct ok2.
             ++ vote_grant_tail r id s m Hlok Hty Hto Hcan.
             ++ vote_reject_tail r id s m Hlok Hto Hterm0.
          -- (* for somebody else: declined.  Both halves of [canVote]'s
                  first two disjuncts are false, so again the third is
                  evaluated and its [MsgPreVote] test has to be decided. *)
             rewrite bool_decide_eq_false_2; last congruence. wp_auto.
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



  (** [MsgVoteResp]: the term preamble, then [r.step(m)].

      The one branch where all three [stepX] can run, so it is also the one
      that needs [own_raft_phys]'s [Hstepfn] conjunct -- without the field
      pinned to the role there is nothing to apply at [r.step(m)].  Three
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
    {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s }}}
      r @! (go.PointerType raft.raft) @! "Step" #m
    {{{ (err : error.t) s', RET #err;
        "Hphys" ∷ own_raft_phys cfg r id s' ∗
        "%Hrefines" ∷ ⌜ ∃ recv,
            (∀ m', m' ∈ recv → m' = abs_msg mtype.VoteResp m) ∧
            step cfg id s recv s' ⌝ ∗
        "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.
  Proof.
    intros Hty Hto Hterm Hcfg.
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
    wp_start_folded as "@". iNamed "Hphys". wp_start_unfold. wp_auto.
    wp_apply (wp_traceReceiveMessage with "[$Hmisc]") as "Hmisc".
    assert (bool_decide (m.(raftpb.Message.Term') = W64 0) = false) as Hz
      by by apply bool_decide_eq_false_2.
    rewrite Hz. rewrite bool_decide_eq_false_2; last done. wp_auto.
    destruct (decide (uint.Z rv.(raft.raft.Term') < uint.Z m.(raftpb.Message.Term')))
      as [Hgt|Hle].
    - (* m.Term > r.Term: step down, then dispatch to stepFollower *)
      assert (bool_decide (uint.Z rv.(raft.raft.Term') <
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
      wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
      wp_auto. rewrite Hlok.
      wp_apply (wp_Logger__logf with "Hlogger").
      { solve_log_method. }
      (* a MsgVoteResp is not from a leader: not MsgApp/Heartbeat/Snap *)
      rewrite Hn3. wp_auto.
      (* not MsgHeartbeat, not MsgSnap either, so the else arm runs
         becomeFollower(m.Term, None) rather than adopting a leader *)
      rewrite Hn8. wp_auto.
      rewrite Hn7. wp_auto.
      (* re-seal for becomeFollower *)
      iAssert (own_raft_phys cfg r id s)
        with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]" as "Hphys".
      { iApply (own_raft_phys_intro with
          "Hlogger Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc"); done. }
      wp_apply (P.wp_raft__becomeFollower with "[$Hphys]") as "Hphys".
      (* the model step: a VoteResp is not from_leader, so no leader is
         adopted and the new lead is 0 *)
      assert (step cfg id s [abs_msg mtype.VoteResp m]
                (become_follower s m.(raftpb.Message.Term') (W64 0))) as Hsd.
      { replace (W64 0) with
          (if from_leader (abs_msg mtype.VoteResp m).(msg.ty)
           then (abs_msg mtype.VoteResp m).(msg.from) else W64 0) by done.
        replace m.(raftpb.Message.Term') with
          (abs_msg mtype.VoteResp m).(msg.term) by done.
        apply step_higher_term.
        - rewrite /abs_msg /= -Hterm0. exact Hgt.
        - rewrite /abs_msg /=. exact Hto. }
      wp_hidden (iNamedSuffix "Hphys" "1").
      (* the type switch: none of its four cases matches a MsgVoteResp, so
         control reaches the default arm r.step(m) *)
      rewrite Hn0. wp_auto.
      rewrite Hn20. wp_auto.
      rewrite Hn22. wp_auto.
      rewrite Hn17. wp_auto.
      rewrite Hn5. wp_auto.
      (* the default arm, [r.step(m)].  [Hstepfn1] pins the field: the
         step-down made the role [Follower], so [step_func_of] is
         [stepFollower]. *)
      assert (rv0.(raft.raft.step') = functions raft.stepFollower []) as Hsf
        by (rewrite Hstepfn1 //).
      rewrite Hsf.
      iAssert (own_raft_phys cfg r id
                 (become_follower s m.(raftpb.Message.Term') (W64 0)))
        with "[Hr1 Htrk1 Hlog1 Hmsgs1 Hmsgs_cap1 HmsgsAA1 HmsgsAA_cap1 Hmisc1]"
        as "Hphys".
      { iApply (own_raft_phys_intro with
          "Hlogger1 Hr1 Htrk1 Hlog1 Hmsgs1 Hmsgs_cap1 HmsgsAA1 HmsgsAA_cap1 Hmisc1"); done. }
      wp_apply (P.wp_stepFollower_MsgVoteResp with "[$Hphys]") as (err) "[Hphys %Herrn]".
      { done. }
      (* [stepFollower] returned [nil], so the error check falls through to
         the trailing [return nil]. *)
      rewrite Herrn. wp_auto.
      iApply ("HΦ" $! interface.nil
                (become_follower s m.(raftpb.Message.Term') (W64 0))).
      iFrame "Hphys". iPureIntro. split; last done.
      exists [abs_msg mtype.VoteResp m]. split; last exact Hsd.
      recv_elem.
    - (* m.Term ≤ r.Term *)
      assert (bool_decide (uint.Z rv.(raft.raft.Term') <
                           uint.Z m.(raftpb.Message.Term')) = false) as Hb
        by by apply bool_decide_eq_false_2.
      rewrite Hb Htf. wp_auto.
      destruct (decide (uint.Z m.(raftpb.Message.Term') <
                        uint.Z rv.(raft.raft.Term'))) as [Hlt|Hnlt].
      + (* m.Term < r.Term.  [checkQuorum] and [preVote] are both off and a
           [MsgVoteResp] is neither [MsgPreVote] nor [MsgStorageAppendResp],
           so every arm is skipped but the last, which only logs; then
           [return nil].  Nothing changed: [step_refl]. *)
        assert (bool_decide (uint.Z m.(raftpb.Message.Term') <
                             uint.Z rv.(raft.raft.Term')) = true) as Hb2
          by by apply bool_decide_eq_true_2.
        rewrite Hb2. rewrite bool_decide_eq_true_2 //. wp_auto.
        rewrite HnoCheckQuorum. wp_auto.
        rewrite HnoPreVote. wp_auto.
        rewrite Hn17. wp_auto.
        rewrite Hn20. wp_auto.
        wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
        wp_auto. rewrite Hlok.
        wp_apply (wp_Logger__logf with "Hlogger").
        { solve_log_method. }
        iApply ("HΦ" $! interface.nil s).
        iSplitL "Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc".
        { iApply (own_raft_phys_intro with
          "Hlogger Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc"); done. }
        iPureIntro. split; last done.
        exists []. split; last apply step_refl.
        recv_elem.
      + (* m.Term = r.Term: the preamble does nothing and control reaches the
           type switch, whose default arm is [r.step(m)]. *)
        assert (bool_decide (uint.Z m.(raftpb.Message.Term') <
                             uint.Z rv.(raft.raft.Term')) = false) as Hb2
          by by apply bool_decide_eq_false_2.
        rewrite Hb2 Htf. wp_auto.
        assert (m.(raftpb.Message.Term') = s.(nstate.term)) as Hteq
          by (rewrite -Hterm0; word).
        rewrite Hn0. wp_auto.
        rewrite Hn20. wp_auto.
        rewrite Hn22. wp_auto.
        rewrite Hn17. wp_auto.
        rewrite Hn5. wp_auto.
        (* the default arm, [r.step(m)].  Unlike the higher-term branch the
           role is untouched, so all three [stepX] are possible. *)
        iAssert (own_raft_phys cfg r id s)
          with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]"
          as "Hphys".
        { iApply (own_raft_phys_intro with
          "Hlogger Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc"); done. }
        destruct s.(nstate.role) eqn:Hrole.
        * (* Follower: [stepFollower] has no [MsgVoteResp] arm. *)
          assert (rv.(raft.raft.step') = functions raft.stepFollower []) as Hsf
            by (rewrite Hstepfn ?Hrole //).
          rewrite Hsf.
          wp_apply (P.wp_stepFollower_MsgVoteResp with "[$Hphys]")
            as (err) "[Hphys %Herrn]".
          { done. }
          rewrite Herrn. wp_auto.
          iApply ("HΦ" $! interface.nil s). iFrame "Hphys".
          iPureIntro. split; last done.
          exists []. split; last apply step_refl.
          recv_elem.
        * (* Candidate: [stepCandidate] records the vote and may win or lose
             in the same call. *)
          assert (rv.(raft.raft.step') = functions raft.stepCandidate []) as Hsf
            by (rewrite Hstepfn ?Hrole //).
          rewrite Hsf.
          wp_apply (P.wp_stepCandidate_MsgVoteResp with "[$Hphys]")
            as (err s') "(Hphys & %Hres & %Herrn)".
          { done. }
          { exact Hto. }
          { exact Hteq. }
          { exact Hrole. }
          { exact Hcfg. }
          rewrite Herrn. wp_auto.
          iApply ("HΦ" $! interface.nil s'). iFrame "Hphys".
          iPureIntro. split; last done.
          exists [abs_msg mtype.VoteResp m]. split.
          { recv_elem. }
          destruct Hres as (won & lost & ms & Hms & Hwon & Hlost & ->).
          rewrite /vote_resp_result.
          destruct won.
          { eapply (step_record_then_win cfg id s (abs_msg mtype.VoteResp m) ms).
            - done.
            - rewrite /abs_msg /=. exact Hto.
            - rewrite /abs_msg /=. exact Hteq.
            - exact Hrole.
            - simpl. exact Hms.
            - simpl. by apply Hwon. }
          destruct lost.
          { eapply (step_record_then_lose cfg id s (abs_msg mtype.VoteResp m)).
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
          assert (rv.(raft.raft.step') = functions raft.stepLeader []) as Hsf
            by (rewrite Hstepfn ?Hrole //).
          rewrite Hsf.
          wp_apply (P.wp_stepLeader_MsgVoteResp with "[$Hphys]")
            as (err) "[Hphys %Herrn]".
          { done. }
          rewrite Herrn. wp_auto.
          iApply ("HΦ" $! interface.nil s). iFrame "Hphys".
          iPureIntro. split; last done.
          exists []. split; last apply step_refl.
          recv_elem.
  Qed.

End branches.

(** [Collection W] is section-scoped but the [Set] that names it is not, and
    [wp_raft__Step]'s type is closed -- forcing W's variables into it would
    add binders the signature does not have.  Restore the prelude default. *)
Set Default Proof Using "Type".

  (** The top-level dispatch: the one triple in [STEP], and **the one place in
      this development where ghost state is updated**.  Each branch lemma
      hands back a pure [step] witness together with the list of messages it
      consumed; here that becomes a single [own_raft_ghost_step].

      [iApply wp_fupd] up front is what makes that possible: the ghost update
      has to happen after the branch lemma returns, when the goal would
      otherwise be the bare postcondition with no fancy update to absorb. *)
  Lemma wp_raft__Step : wp_raft__Step_body.
  Proof.
    intros_ambient.
    intros cfg γ r id s m.
    intros Helection Hin Hhup Hvote Hvoteresp.
    iIntros (Φ) "(#Hinit & Hphys & Hghost & #Hm & #Hctx) HΦ".
    iApply wp_fupd.
    destruct Helection as [Hty | [Hty | Hty]].
    - (* MsgHup: a local message, handled by [hup]. *)
      destruct (Hhup Hty) as [Hmterm Hnowrap].
      wp_apply (wp_Step_MsgHup cfg with "[$Hphys]"); [done..|].
      iIntros (err s') "(Hphys & %Hst & %Herr)".
      iMod (own_raft_ghost_step_0 _ _ _ _ _ Hst with "Hghost") as "Hghost".
      iModIntro. iApply ("HΦ" $! err s'). iFrame.
      iPureIntro. split; [by eexists []|done].
    - (* MsgVote: answer the vote request, stepping down first if needed. *)
      destruct (Hvote Hty) as (Hto & Hterm & Hfnz).
      iDestruct ("Hm" $! mtype.Vote with "[]") as "#Hm'".
      { iPureIntro. rewrite Hty. apply mtype_of_MsgVote. }
      wp_apply (wp_Step_MsgVote cfg with "[$Hphys $Hctx]"); [done..|].
      iIntros (err s') "(Hphys & %Hst & %Herr)".
      destruct Hst as (recv & Hrecv & Hstep).
      iMod (own_raft_ghost_step _ _ _ _ _ _ Hstep with "[] Hghost") as "Hghost".
      { iApply big_sepL_intro. iIntros "!> %k %m' %Hk".
        rewrite (Hrecv m'); [iFrame "#"|by eapply list_elem_of_lookup_2]. }
      iModIntro. iApply ("HΦ" $! err s'). iFrame.
      iPureIntro. split; [by eexists recv|done].
    - (* MsgVoteResp: tally the vote, possibly winning or losing. *)
      destruct (Hvoteresp Hty) as [Hto Hterm].
      iDestruct ("Hm" $! mtype.VoteResp with "[]") as "#Hm'".
      { iPureIntro. rewrite Hty. apply mtype_of_MsgVoteResp. }
      wp_apply (wp_Step_MsgVoteResp cfg with "[$Hphys]"); [done..|].
      iIntros (err s') "(Hphys & %Hst & %Herr)".
      destruct Hst as (recv & Hrecv & Hstep).
      iMod (own_raft_ghost_step _ _ _ _ _ _ Hstep with "[] Hghost") as "Hghost".
      { iApply big_sepL_intro. iIntros "!> %k %m' %Hk".
        rewrite (Hrecv m'); [iFrame "#"|by eapply list_elem_of_lookup_2]. }
      iModIntro. iApply ("HΦ" $! err s'). iFrame.
      iPureIntro. split; [by eexists recv|done].
  Qed.

End StepProof.
