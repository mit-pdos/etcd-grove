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
    wp_start as "@".
    iNamed "Hphys".
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
    iAssert (own_raft_phys cfg r id s)
    with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]" as "Hphys".
    { rewrite /own_raft_phys. iFrame "∗#%". }
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
      [rewrite /log_methods; set_solver|];
    wp_apply P.wp_voteRespMsgType; [done|];
    iAssert (own_raft_phys cfg r_ id_ s_)
      with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]"
      as "Hphys";
      [rewrite /own_raft_phys; iFrame "∗#%"|];
    wp_apply (P.wp_raft__send_vote with "[$Hphys]") as "Hphys";
      [done|by right|apply mtype_of_MsgVoteResp|done|w32_ne|];
    iNamedSuffix "Hphys" "2";
    rewrite ty_eq /MsgVote bool_decide_eq_true_2 //;
    wp_auto;
    iApply ("HΦ" $! interface.nil
      (send_msgs (s_ <| nstate.vote := m_.(raftpb.Message.From') |>)
         [msg.mk mtype.VoteResp id_ m_.(raftpb.Message.From')
            m_.(raftpb.Message.Term') false]));
    iSplitL "Hr2 Htrk2 Hlog2 Hmsgs2 Hmsgs_cap2 HmsgsAA2 HmsgsAA_cap2 Hmisc2";
      [rewrite /own_raft_phys /send_msgs /=;
       iEval (simpl) in "Htrk2";
       iFrame "Hr2 ∗#%";
       iPureIntro; first [(split_and!; done)|done]|];
    iPureIntro; split; [|done];
    exists [abs_msg mtype.Vote m_];
    split; [set_solver|];
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
      [rewrite /log_methods; set_solver|];
    wp_apply P.wp_voteRespMsgType; [done|];
    rewrite term_eq;
    iAssert (own_raft_phys cfg r_ id_ s_)
      with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]"
      as "Hphys";
      [rewrite /own_raft_phys; iFrame "∗#%"|];
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
    split; [set_solver|];
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
    wp_start as "@". iNamed "Hphys". wp_auto.
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
    { rewrite /log_methods. set_solver. }
    (* a [MsgVote] is not from a leader, so no leader is adopted *)
    rewrite Hty /MsgVote bool_decide_eq_false_2; last w32_ne. wp_auto.
    rewrite Hty /MsgVote bool_decide_eq_false_2; last w32_ne. wp_auto.
    rewrite Hty /MsgVote bool_decide_eq_false_2; last w32_ne. wp_auto.
    iAssert (own_raft_phys cfg r id s)
      with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]" as "Hphys".
    { rewrite /own_raft_phys. iExists rv, msgs, msgsAA, lok. iFrame "∗#%". }
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
    iNamedSuffix "Hphys" "1".
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
      { rewrite /log_methods. set_solver. }
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
      { rewrite /own_raft_phys. iExists rv0, msgs0, msgsAA0, lok0.
        rewrite /become_follower /= decide_False //. iFrame "∗#%". }
      (* [send] the granted vote response, then record the vote. *)
      wp_apply (P.wp_raft__send_vote with "[$Hphys]") as "Hphys".
      { done. }
      { by right. }
      { apply mtype_of_MsgVoteResp. }
      { done. }
      { w32_ne. }
      iNamedSuffix "Hphys" "2".
      (* [m.Type = MsgVote], so the vote is recorded: [r.Vote := m.From]. *)
      rewrite Hty /MsgVote bool_decide_eq_true_2 //. wp_auto.
      iApply ("HΦ" $! interface.nil
        (send_msgs ((become_follower s m.(raftpb.Message.Term') (W64 0))
                      <| nstate.vote := m.(raftpb.Message.From') |>)
           [msg.mk mtype.VoteResp id m.(raftpb.Message.From')
              m.(raftpb.Message.Term') false])).
      iSplitL "Hr2 Htrk2 Hlog2 Hmsgs2 Hmsgs_cap2 HmsgsAA2 HmsgsAA_cap2 Hmisc2".
      { rewrite /own_raft_phys /send_msgs /become_follower /=.
        iExists _, msgs1, msgsAA1, lok1.
        simpl in Hid2, Hterm2, Hvote2, Hlead2, Hstate2, Houtbox2.
        iEval (simpl) in "Htrk2".
        iFrame "Hr2 ∗#%".
        iPureIntro. first [done | (split_and!; done)]. }
      iPureIntro. split; last done.
      eexists ([abs_msg mtype.Vote m] ++ [abs_msg mtype.Vote m]).
      split.
      { intros m' Hm'. set_solver. }
      eapply step_trans; [exact Hstepdown|exact Hgrant].
    + (* the candidate's log is behind: decline, without recording a vote *)
      wp_auto.
      wp_apply wp_slice_literal. iSplitR; first done. iIntros "% [? _]".
      wp_auto. rewrite Hlok1.
      wp_apply (wp_Logger__logf with "Hlogger1").
      { rewrite /log_methods. set_solver. }
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
      { rewrite /own_raft_phys. iExists rv0, msgs0, msgsAA0, lok0.
        rewrite /become_follower /= decide_False //. iFrame "∗#%". }
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
      { intros m' Hm'. set_solver. }
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
        { rewrite /log_methods. set_solver. }
        (* nothing was sent and nothing changed: dropping is [step_refl]. *)
        iAssert (own_raft_phys cfg r id s)
          with "[Hr Htrk Hlog Hmsgs Hmsgs_cap HmsgsAA HmsgsAA_cap Hmisc]"
          as "Hphys".
        { rewrite /own_raft_phys. iExists rv, msgs, msgsAA, lok. iFrame "∗#%". }
        iApply ("HΦ" $! interface.nil s). iFrame "Hphys".
        iPureIntro. split; last done. exists [].
        split; [set_solver|apply step_drop].
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



  (** [MsgVoteResp]: dispatched to [stepCandidate]. *)
  Lemma wp_Step_MsgVoteResp r id s (m : raftpb.Message.t) :
    m.(raftpb.Message.Type') = MsgVoteResp →
    m.(raftpb.Message.To') = id →
    m.(raftpb.Message.Term') ≠ W64 0 →
    {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s }}}
      r @! (go.PointerType raft.raft) @! "Step" #m
    {{{ (err : error.t) s', RET #err;
        "Hphys" ∷ own_raft_phys cfg r id s' ∗
        "%Hrefines" ∷ ⌜ ∃ recv,
            (∀ m', m' ∈ recv → m' = abs_msg mtype.VoteResp m) ∧
            step cfg id s recv s' ⌝ ∗
        "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.
  Proof.
    (** UNPROVED, and **blocked on shared files** -- not on effort.  There is
        no proof script here because the very first step cannot be taken.

        A [MsgVoteResp] is not handled inline by [Step]: it falls all the way
        through the type switch to the default arm, which calls
        [r.step(m)] -- see the [![raft.stepFunc] (StructFieldRef raft.raft
        "step" ...)] at the end of [raft__Stepⁱᵐᵖˡ] in
        [new/code/go_etcd_io/raft/v3.v].  Three things are missing:

        1. **[own_raft_phys] says nothing about [r.step].**  [inv_raft_phys.v]
           carries a comment promising that "the step function stored in
           [r.step] is determined by the role; ... we record which of the
           three [stepX] functions it is by the role", but there is no such
           conjunct: [rv.(raft.raft.step')] is completely unconstrained.  That
           is why [proof_raft__becomeFollower.v] can re-seal with
           [iExists (rv <| raft.raft.step' := _ |>)].  So [wp_auto] reaches
           [#rv.(raft.raft.step') #r #m] and there is nothing to apply --
           the call cannot be stepped at all.

        2. **The role at the call is not necessarily [role.Candidate].**  On
           [m.Term > r.Term] the term preamble runs [becomeFollower] (a
           [MsgVoteResp] is not from a leader), so the role is
           [role.Follower]; on [m.Term = r.Term] the role is whatever
           [s.(nstate.role)] was, i.e. possibly [Follower] or [Leader].  Only
           the candidate case dispatches to [stepCandidate], so this branch
           also needs [stepFollower]/[stepLeader] specs for [MsgVoteResp]
           (both are no-ops returning [nil], falling off the end of their
           type switches).  Neither exists.

        3. **[P.wp_stepCandidate_MsgVoteResp] requires [id ∈ cfg], and it
           cannot be discharged here.**  It is in none of the three places it
           could come from: not [own_raft_phys], not [wp_raft__Step_body]'s
           premises, and not this lemma's.  [spec_stepCandidate_MsgVoteResp.v]
           says the obligation is "threaded in from the caller", naming
           [hup]/[campaign] -- but [Step] is the outermost caller, so there is
           nobody left to thread it from.  It has to be added either to
           [own_raft_phys] or to [wp_raft__Step_body].

        Nothing here is weakened or assumed away: no [Axiom] was added and
        the statement above is the one [wp_raft__Step] consumes. *)
  Admitted.

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
    intros Helection Hhup Hvote Hvoteresp.
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
