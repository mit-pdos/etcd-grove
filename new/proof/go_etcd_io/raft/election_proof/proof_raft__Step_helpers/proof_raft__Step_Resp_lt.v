(** The lower-term case of [Step]'s [MsgAppResp] and [MsgHeartbeatResp]
    branches, for both types at once, in its own file so that it checks in
    parallel with the other term cases -- see
    [proof_raft__Step_MsgAppResp.v] and [proof_raft__Step_MsgHeartbeatResp.v],
    which combine them.  Proof structure, not specification: no
    [Module Type], no [Parameter]; only files in this directory may
    [Require] it. *)
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_resp_lemmas.

Module StepRespLt (P : STEP_POSTULATES).
Import P.

Section branches.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).

Implicit Type s : nstate.t.

  Local Ltac ne_ty Hty :=
    apply bool_decide_eq_false_2;
    destruct Hty as [Ht|Ht]; rewrite Ht; w32_ne.

  (** [m.Term < r.Term] for a [MsgAppResp] or [MsgHeartbeatResp]: with
      [checkQuorum] and [preVote] both off, and the type neither
      [MsgPreVote] nor [MsgStorageAppendResp], the stale message is only
      logged, then [return nil].  [step_refl], nothing received. *)
  Lemma wp_Step_Resp_lt r id s (m : raftpb.Message.t)
      (ents : list raftpb.Entry.t) (ty : mtype.t) :
    m.(raftpb.Message.Type') = MsgAppResp ∨
    m.(raftpb.Message.Type') = MsgHeartbeatResp →
    m.(raftpb.Message.Term') ≠ W64 0 →
    uint.Z m.(raftpb.Message.Term') < uint.Z s.(nstate.term) →
    nstate_wf s →
    {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s }}}
      r @! (go.PointerType raft.raft) @! "Step" #m
    {{{ (err : error.t) s', RET #err;
        "Hphys" ∷ own_raft_phys cfg r id s' ∗
        "%Hwf'" ∷ ⌜ nstate_wf s' ⌝ ∗
        "%Hrefines" ∷ ⌜ ∃ recv,
            (∀ m', m' ∈ recv → m' = abs_msg ty m ents) ∧
            step cfg id (to_pstate s) recv (to_pstate s') ⌝ ∗
        "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.
  Proof.
    intros Hty Hterm Hlt Hwf.
    assert (Hn17 : bool_decide (m.(raftpb.Message.Type') = W32 17) = false) by ne_ty Hty.
    assert (Hn20 : bool_decide (m.(raftpb.Message.Type') = W32 20) = false) by ne_ty Hty.
    assert (Hn8 : bool_decide (m.(raftpb.Message.Type') = W32 8) = false) by ne_ty Hty.
    assert (Hn3 : bool_decide (m.(raftpb.Message.Type') = W32 3) = false) by ne_ty Hty.
    assert (Htf : bool_decide (true = false) = false) by done.
    wp_start_folded as "@". wp_start_unfold. wp_auto.
    wp_apply wp_traceReceiveMessage. try wp_auto.
    assert (bool_decide (m.(raftpb.Message.Term') = W64 0) = false) as Hz
      by by apply bool_decide_eq_false_2.
    rewrite Hz. rewrite bool_decide_eq_false_2; last done. wp_auto.
    wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
    assert (bool_decide (uint.Z s.(nstate.term) <
                         uint.Z m.(raftpb.Message.Term')) = false) as Hb
      by (apply bool_decide_eq_false_2; lia).
    rewrite Hb Htf. wp_auto.
    wp_apply (wp_raft_load_Term with "Hphys") as "Hphys".
    assert (bool_decide (uint.Z m.(raftpb.Message.Term') <
                         uint.Z s.(nstate.term)) = true) as Hb2
      by by apply bool_decide_eq_true_2.
    rewrite Hb2. rewrite bool_decide_eq_true_2 //. wp_auto.
    (* [checkQuorum] is off; with pre-vote on the type test runs and is
       false, so the MsgHeartbeat/MsgApp response is not sent *)
    wp_apply (wp_raft_load_checkQuorum with "Hphys") as "Hphys".
    wp_apply (wp_raft_load_preVote with "Hphys") as "Hphys".
    destruct (s.(nstate.prevote)); wp_auto;
      [rewrite Hn8; wp_auto; rewrite Hn3; wp_auto|].
    all: rewrite Hn17; wp_auto; rewrite Hn20; wp_auto.
    all: (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_apply (wp_raft_load_Term with "Hphys") as "Hphys"; wp_raft_log).
    all: iApply ("HΦ" $! interface.nil s); iFrame "Hphys".
    all: iPureIntro; split; first exact Hwf; split; last done.
    all: exists []; split; last apply step_refl.
    all: intros ? Hin; by apply elem_of_nil in Hin.
  Qed.

End branches.

End StepRespLt.
