(** One term case of [Step]'s [MsgSnap] branch (the incoming term is stale:
    logged and dropped), in its own file so that it checks in parallel with
    the others; [proof_raft__Step_MsgSnap.v] combines them.  Proof
    structure, not specification: no [Module Type], no [Parameter]; only
    files in this directory may [Require] it. *)
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_repl_lemmas.

Module StepMsgSnapLt (P : STEP_POSTULATES).
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

  Lemma wp_Step_MsgSnap_lt r id s (m : raftpb.Message.t)
      (sv : raftpb.Snapshot.t) (voters : list w64) :
    m.(raftpb.Message.Type') = MsgSnap →
    m.(raftpb.Message.To') = id →
    m.(raftpb.Message.Term') ≠ W64 0 →
    nstate_wf s →
    (* this file: the incoming term is stale: logged and dropped *)
    uint.Z m.(raftpb.Message.Term') < uint.Z s.(nstate.term) →
    {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s }}}
      r @! (go.PointerType raft.raft) @! "Step" #m
    {{{ (err : error.t) s', RET #err;
        "Hphys" ∷ own_raft_phys cfg r id s' ∗
        "%Hwf'" ∷ ⌜ nstate_wf s' ⌝ ∗
        "%Hrefines" ∷ ⌜ ∃ recv,
            (∀ m', m' ∈ recv → m' = abs_snap m sv voters) ∧
            step cfg id (to_pstate s) recv (to_pstate s') ⌝ ∗
        "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.
  Proof.
    intros Hty Hto Hterm Hwf Hlt.
    assert (Hty7 : m.(raftpb.Message.Type') = W32 7) by (rewrite Hty //).
    assert (Hn17 : bool_decide (m.(raftpb.Message.Type') = W32 17) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty7; w32_ne).
    assert (Hn20 : bool_decide (m.(raftpb.Message.Type') = W32 20) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty7; w32_ne).
    assert (Hn8 : bool_decide (m.(raftpb.Message.Type') = W32 8) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty7; w32_ne).
    assert (Hn3 : bool_decide (m.(raftpb.Message.Type') = W32 3) = false)
      by (apply bool_decide_eq_false_2; rewrite Hty7; w32_ne).
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
    (* (checkQuorum || preVote) && (MsgHeartbeat || MsgApp): [checkQuorum]
       is off; with pre-vote on, the type test is false *)
    wp_apply (wp_raft_load_checkQuorum with "Hphys") as "Hphys".
    wp_apply (wp_raft_load_preVote with "Hphys") as "Hphys".
    destruct (s.(nstate.prevote)); wp_auto;
      [rewrite Hn8; wp_auto; rewrite Hn3; wp_auto|].
    (* not MsgPreVote, not MsgStorageAppendResp: only the log line *)
    all: rewrite Hn17; wp_auto; rewrite Hn20; wp_auto.
    all: (wp_apply (wp_raft_load_id with "Hphys") as "Hphys"; wp_apply (wp_raft_load_Term with "Hphys") as "Hphys"; wp_raft_log).
    all: iApply ("HΦ" $! interface.nil s); iFrame "Hphys".
    all: iPureIntro; split; first exact Hwf; split; last done.
    all: exists []; split; last apply step_refl.
    all: recv_elem.
  Qed.

End branches.

End StepMsgSnapLt.
