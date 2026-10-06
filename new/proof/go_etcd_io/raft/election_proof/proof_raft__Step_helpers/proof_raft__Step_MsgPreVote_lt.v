(** One term case of [Step]'s [MsgPreVote] branch (2026-10-04): the
    incoming term is stale.  In its own file so that it checks in parallel
    with the others; [proof_raft__Step_MsgPreVote.v] combines them.  Proof
    structure, not specification: no [Module Type], no [Parameter]; only
    files in this directory may [Require] it. *)
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_prevote_lemmas.

Module StepMsgPreVoteLt (P : STEP_POSTULATES).
Import P.

Section branches.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).

Implicit Type s : nstate.t.

  (** [MsgPreVote] with [m.Term < r.Term]: the stale arm answers with a
      rejecting [MsgPreVoteResp] at [r.Term] (raft.go:1144-1152), a free
      message ([step_send_free]); [r.Term > m.Term], so it is not [0]. *)
  Lemma wp_Step_MsgPreVote_lt r id s (m : raftpb.Message.t) :
    m.(raftpb.Message.Type') = MsgPreVote →
    m.(raftpb.Message.To') = id →
    m.(raftpb.Message.Term') ≠ W64 0 →
    m.(raftpb.Message.From') ≠ W64 0 →
    (* this file: the incoming term is stale *)
    uint.Z m.(raftpb.Message.Term') < uint.Z s.(nstate.term) →
    nstate_wf s →
    {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s }}}
      r @! (go.PointerType raft.raft) @! "Step" #m
    {{{ (err : error.t) s', RET #err;
        "Hphys" ∷ own_raft_phys cfg r id s' ∗
        "%Hwf'" ∷ ⌜ nstate_wf s' ⌝ ∗
        "%Hrefines" ∷ ⌜ step cfg id (to_pstate s) [] (to_pstate s') ⌝ ∗
        "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.
  Proof.
    intros Hty Hto Hterm Hfnz Hlt0 Hwf.
    assert (Hty17 : m.(raftpb.Message.Type') = W32 17) by (rewrite Hty //).
    assert (Hn8 : bool_decide (m.(raftpb.Message.Type') = W32 8) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty17; w32_ne).
    assert (Hn3 : bool_decide (m.(raftpb.Message.Type') = W32 3) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty17; w32_ne).
    assert (Hy17 : bool_decide (m.(raftpb.Message.Type') = W32 17) = true)
      by (apply bool_decide_eq_true_2; exact Hty17).
    assert (Hs0 : s.(nstate.term) ≠ W64 0) by (intros H0; rewrite H0 in Hlt0; word).
    wp_start_folded as "@". wp_start_unfold. wp_auto.
    wp_apply wp_traceReceiveMessage. try wp_auto.
    assert (bool_decide (m.(raftpb.Message.Term') = W64 0) = false) as Hz
      by by apply bool_decide_eq_false_2.
    rewrite Hz. rewrite bool_decide_eq_false_2; last done. wp_auto.
    wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
    assert (bool_decide (uint.Z s.(nstate.term) <
                         uint.Z m.(raftpb.Message.Term')) = false) as Hb
      by (apply bool_decide_eq_false_2; lia).
    rewrite Hb. rewrite bool_decide_eq_false_2; last done. wp_auto.
    wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
    assert (bool_decide (uint.Z m.(raftpb.Message.Term') <
                         uint.Z s.(nstate.term)) = true) as Hb2
      by by apply bool_decide_eq_true_2.
    rewrite Hb2. rewrite bool_decide_eq_true_2 //. wp_auto.
    (* (checkQuorum || preVote) && (MsgHeartbeat || MsgApp): false either way *)
    wp_apply (wp_raft_load_checkQuorum with "Hphys") as "Hphys".
    wp_apply (wp_raft_load_preVote with "Hphys") as "Hphys".
    destruct (s.(nstate.prevote)); wp_auto;
      [rewrite Hn8; wp_auto; rewrite Hn3; wp_auto|].
    (* MsgPreVote: reject at [r.Term] *)
    all: rewrite Hy17; wp_auto.
    all: wp_apply (wp_raft_load_raftLog with "Hphys") as "Hphys".
    all: wp_hidden (iDestruct (own_raft_phys_log_same with "Hphys")
                      as "(Hlog1 & Hback)").
    all: wp_apply (wp_raftLog__lastEntryID _ _ with "[$Hlog1]") as "%lastID [Hlog1 _]".
    all: wp_hidden (iDestruct ("Hback" with "Hlog1") as "Hphys").
    all: (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_apply (wp_raft_load_Vote with "Hphys") as "Hphys"; wp_apply (wp_raft_load_Term with "Hphys") as "Hphys"; wp_raft_log).
    all: wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
    all: wp_apply (P.wp_raft__send _ _ _ _ _ [] with "[$Hphys]") as "Hphys";
      [ by left
      | left; exists mtype.PreVoteResp; split_and!;
          [by right; right; right | apply mtype_of_MsgPreVoteResp | (simpl; exact Hs0)
          | intros [Hc|Hc]; revert Hc; w32_ne | done]
      | iSplitR; [iApply own_slice_nil | iApply send_no_snap; simpl; w32_ne]
      | ].
    all: iApply ("HΦ" $! interface.nil _); iFrame "Hphys".
    all: iPureIntro; (split; [by apply nstate_wf_send_msgs|split; [|done]]).
    all: rewrite to_pstate_send_msgs; apply step_send_free; [by right|done].
  Qed.

End branches.

End StepMsgPreVoteLt.
