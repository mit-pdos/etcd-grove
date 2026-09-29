(** One case of [Step]'s [MsgVote] branch with [m.Term ≤ r.Term], in its own
    file so that it checks in parallel with the others -- see
    [proof_raft__Step_MsgVote_le.v], which combines them, and
    [notes/decisions.md] (2026-09-17; 2026-09-18 for why this directory
    exists).  Proof structure, not specification:
    no [Module Type], no [Parameter]; only [proof_raft__Step_MsgVote_le.v]
    may [Require] this file. *)
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__Step.

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
      as [wp_raft_log] in [inv_raft_phys.v]. *)

  (** Grant the vote in the *current* term: log, [send] the response, and
      record [r.Vote := m.From].  [can] is the protocol-level [pcan_vote] of
      [to_pstate s_]; [wf_] is [nstate_wf s_].  Starts with the log closed
      (["Hphys"] whole). *)
  Local Ltac vote_grant_tail id_ s_ m_ ty_eq to_eq can wf_ :=
    try wp_auto;
    (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_apply (wp_raft_load_Vote with "Hphys") as "Hphys"; wp_apply (wp_raft_load_Term with "Hphys") as "Hphys"; wp_raft_log);
    wp_apply P.wp_voteRespMsgType; [done|];
    wp_apply (P.wp_raft__send with "[$Hphys]") as "Hphys";
      [done|left; exists mtype.VoteResp; split_and!;
            [by right|apply mtype_of_MsgVoteResp|done|w32_ne|done]|];
    rewrite ty_eq /MsgVote bool_decide_eq_true_2 //;
    try wp_auto;
    (* [r.electionElapsed = 0; r.Vote = m.From] *)
    wp_apply (wp_raft_store_electionElapsed with "Hphys") as "Hphys";
    wp_apply (wp_raft_store_Vote with "Hphys") as "Hphys";
    iApply ("HΦ" $! interface.nil
      (send_msgs (s_ <| nstate.vote := m_.(raftpb.Message.From') |>)
         [msg.mk mtype.VoteResp id_ m_.(raftpb.Message.From')
            m_.(raftpb.Message.Term') false]));
    (* the state is given explicitly: the stores leave
       [send_msgs s_ out <| vote := From |>], with [out] in [send]'s form of
       the message literal; only conversion (after [destruct s_]) relates it
       to the [msg.mk] form named here. *)
    iSplitL "Hphys";
      [iApply (own_raft_phys_eq with "Hphys"); by destruct s_|];
    iPureIntro; split; [exact wf_|]; split; [|done];
    exists [abs_msg mtype.Vote m_];
    split; [recv_elem|];
    rewrite to_pstate_send_msgs to_pstate_vote;
    replace m_.(raftpb.Message.Term') with s_.(nstate.term) by congruence;
    apply (step_grant_vote cfg id_ (abs_msg mtype.Vote m_) (to_pstate s_));
      [done|exact to_eq|done|(rewrite /abs_msg /=; congruence)|exact can].

  (** Decline: log, then [send] a rejection carrying [r.Term].  Always legal,
      so there is no side condition beyond the message being a [MsgVote]
      addressed to us.  Starts with the log closed (["Hphys"] whole). *)
  Local Ltac vote_reject_tail id_ s_ m_ to_eq wf_ :=
    try wp_auto;
    (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_apply (wp_raft_load_Vote with "Hphys") as "Hphys"; wp_apply (wp_raft_load_Term with "Hphys") as "Hphys"; wp_raft_log);
    (* [Term: r.Term] and the [voteRespMsgType] call, in whichever order the
       struct literal evaluates them *)
    wp_apply (wp_raft_load_Term with "Hphys") as "Hphys";
    wp_apply P.wp_voteRespMsgType; [done|];
    (* The response carries [s.term], so [send]'s [m.Term ≠ 0] premise is the
       incoming message's, transported along [m.Term = s.term].  The [simpl] is not
       optional: the premise is stated about the *message literal*, so the
       goal is [{| ... |}.(Message.Term') ≠ W64 0] and [congruence] -- unlike
       [done]/[assumption] -- does not see through the projection. *)
    wp_apply (P.wp_raft__send with "[$Hphys]") as "Hphys";
      [done|left; exists mtype.VoteResp; split_and!;
            [by right|apply mtype_of_MsgVoteResp|(simpl; congruence)|w32_ne|done]|];
    iApply ("HΦ" $! interface.nil _); iFrame "Hphys";
    iPureIntro; split; [exact wf_|]; split; [|done];
    exists [abs_msg mtype.Vote m_];
    split; [recv_elem|];
    rewrite to_pstate_send_msgs;
    apply (step_reject_vote cfg id_ (abs_msg mtype.Vote m_) (to_pstate s_));
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
    (* [r.step] matches the role and nothing is on loan *)
    nstate_wf s →
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
        "%Hwf'" ∷ ⌜ nstate_wf s' ⌝ ∗
        (* [recv] is whatever this branch consumed -- nothing, or the incoming
           message once or twice.  Naming its elements rather than the list
           lets [wp_raft__Step] discharge the [is_message] side of
           [own_raft_ghost_step] from the single fact it holds about [m]. *)
        "%Hrefines" ∷ ⌜ ∃ recv,
            (∀ m', m' ∈ recv → m' = abs_msg mtype.Vote m) ∧
            step cfg id (to_pstate s) recv (to_pstate s') ⌝ ∗
        "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.
  Proof.
    intros Hty Hto Hterm Hfnz Heq0 Hv00 Hwf.
    pose proof Hwf as [Hsfw Hlent].
    wp_start_folded as "@". wp_start_unfold. wp_auto.
    assert (Hle : ¬ (uint.Z s.(nstate.term) < uint.Z m.(raftpb.Message.Term')))
      by (rewrite Heq0; lia).
    assert (Hnlt : ¬ (uint.Z m.(raftpb.Message.Term') < uint.Z s.(nstate.term)))
      by (rewrite Heq0; lia).
    wp_apply wp_traceReceiveMessage. try wp_auto.
    (* [m.Term ≠ 0], so the first arm of the term preamble is skipped. *)
    assert (bool_decide (m.(raftpb.Message.Term') = W64 0) = false) as Hz
    by by apply bool_decide_eq_false_2.
    rewrite Hz. rewrite bool_decide_eq_false_2; last done. wp_auto.
    wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
      assert (bool_decide (uint.Z s.(nstate.term) <
                           uint.Z m.(raftpb.Message.Term')) = false) as Hb
        by by apply bool_decide_eq_false_2.
      rewrite Hb. rewrite bool_decide_eq_false_2; last done. wp_auto.
      wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
        assert (bool_decide (uint.Z m.(raftpb.Message.Term') <
                             uint.Z s.(nstate.term)) = false) as Hb2
          by by apply bool_decide_eq_false_2.
        rewrite Hb2. rewrite bool_decide_eq_false_2; last done. wp_auto.
        (* the type switch: not MsgHup / MsgStorageAppendResp /
           MsgStorageApplyResp, not MsgPreVote, but MsgVote *)
        rewrite Hty /MsgVote bool_decide_eq_false_2; last w32_ne. wp_auto.
        (* [canVote] is the model's [can_vote]: the Go expression's third
           disjunct needs [MsgPreVote] and is dead here. *)
          wp_apply (wp_raft_load_Vote with "Hphys") as "Hphys".
          rewrite Hv00 bool_decide_eq_false_2; last congruence. wp_auto.
          wp_apply (wp_raft_load_Vote with "Hphys") as "Hphys".
          rewrite Hv00 bool_decide_eq_true_2 //. wp_auto.
          wp_apply (wp_raft_load_lead with "Hphys") as "Hphys".
          destruct (decide (s.(nstate.lead) = W64 0)) as [Hl0|Hl0].
          -- (* and recognises no leader: [canVote] *)
             rewrite Hl0 bool_decide_eq_true_2 //. wp_auto.
             assert (Hcan : pcan_vote (to_pstate s) m.(raftpb.Message.From'))
               by (rewrite /pcan_vote /=; right; split; congruence).
             (* each [raftLog] call: load the field, open the log, call,
                close it again -- the next field load needs ["Hphys"] *)
             wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
             wp_hidden (iDestruct (own_raft_phys_log_same with "Hphys")
                          as "[Hlog Hlogback]").
             wp_apply (wp_raftLog__lastEntryID _ _ with "[$Hlog]")
               as "%lastID2 Hlog".
             wp_hidden (iDestruct ("Hlogback" with "Hlog") as "Hphys").
             wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
             wp_hidden (iDestruct (own_raft_phys_log_same with "Hphys")
                          as "[Hlog Hlogback]").
             wp_apply (wp_raftLog__isUpToDate _ _ _ with "[$Hlog]") as "%ok2 Hlog".
             wp_hidden (iDestruct ("Hlogback" with "Hlog") as "Hphys").
             destruct ok2.
             ++ vote_grant_tail id s m Hty Hto Hcan Hwf.
             ++ vote_reject_tail id s m Hto Hwf.
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
             wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
             wp_hidden (iDestruct (own_raft_phys_log_same with "Hphys")
                          as "[Hlog Hlogback]").
             wp_apply (wp_raftLog__lastEntryID _ _ with "[$Hlog]")
               as "%lastID2 Hlog".
             wp_hidden (iDestruct ("Hlogback" with "Hlog") as "Hphys").
             vote_reject_tail id s m Hto Hwf.
  Qed.

End branches.

End StepMsgVoteEqNovote.
