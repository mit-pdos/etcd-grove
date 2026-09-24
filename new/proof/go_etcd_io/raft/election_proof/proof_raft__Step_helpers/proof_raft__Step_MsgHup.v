(** One branch of [Step]'s proof, in its own file so that the three branches
    check in parallel under [make -j] -- each is a few minutes of [wp_auto]
    over the same 100k-node body, and in one file they ran back to back.

    This is **proof structure, not specification**: [Step] has exactly one
    spec, in [spec_raft__Step.v], and this module has no [Module Type] and no
    [Parameter].  Nothing but [proof_raft__Step.v], or another file in this
    directory, may [Require] it; see [notes/decisions.md] (2026-09-17, and
    2026-09-18 for why the helpers moved out of the top-level directory). *)
Require Export New.proof.go_etcd_io.raft.election_proof.postulates_raft__Step.

Module StepMsgHup (P : STEP_POSTULATES).
Import P.

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
    (* [r.step] matches the role and nothing is on loan *)
    nstate_wf s →
    {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s }}}
      r @! (go.PointerType raft.raft) @! "Step" #m
    {{{ (err : error.t) s', RET #err;
        "Hphys" ∷ own_raft_phys cfg r id s' ∗
        "%Hwf'" ∷ ⌜ nstate_wf s' ⌝ ∗
        "%Hrefines" ∷ ⌜ step cfg id (to_pstate s) [] (to_pstate s') ⌝ ∗
        "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.
  Proof.
    intros Hty Hterm Hnowrap Hwf.
    wp_start as "@". wp_auto.
    wp_apply wp_traceReceiveMessage. try wp_auto.
    (* [m.Term = 0] (a local message), so the term preamble is skipped. *)
    rewrite Hterm !bool_decide_eq_true_2 //.
    wp_auto.
    (* the type switch selects the [MsgHup] case *)
    rewrite Hty /MsgHup bool_decide_eq_true_2 //.
    wp_auto.
    (* no pre-vote, so this is a plain [hup(campaignElection)] *)
    wp_raft_field.
    wp_apply (P.wp_raft__hup with "[$Hphys]") as "%s' (Hphys & %Hwf' & %Hstep)".
    { done. }
    { exact Hnowrap. }
    { exact Hwf. }
    iApply ("HΦ" $! interface.nil s'). iFrame "Hphys".
    iPureIntro. split; [exact Hwf' | split; [exact Hstep | done]].
  Qed.

End branches.

End StepMsgHup.
