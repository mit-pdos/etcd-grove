(** [Step]'s [MsgPreVoteResp] branch (2026-10-04), combining the three
    term cases, each in its own file so that they check in parallel.  Proof
    structure, not specification: no [Module Type], no [Parameter]; only
    [proof_raft__Step.v] may [Require] this file. *)
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgPreVoteResp_gt.
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgPreVoteResp_eq.
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgPreVoteResp_lt.

Module StepMsgPreVoteResp (P : STEP_POSTULATES).
Import P.

Module G := StepMsgPreVoteRespGt P.
Module E := StepMsgPreVoteRespEq P.
Module L := StepMsgPreVoteRespLt P.

Section branches.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).

Implicit Type s : nstate.t.

  (** [MsgPreVoteResp]: a rejection of a higher term steps the node down
      ([step_higher_term]); otherwise only a pre-candidate acts on it
      ([step_prevote_resp_result]); a stale one is dropped. *)
  Lemma wp_Step_MsgPreVoteResp r id s (m : raftpb.Message.t)
      (ents : list raftpb.Entry.t) :
    m.(raftpb.Message.Type') = MsgPreVoteResp →
    m.(raftpb.Message.To') = id →
    m.(raftpb.Message.Term') ≠ W64 0 →
    uint.Z s.(nstate.term) + 1 < 2 ^ 64 →
    id ∈ cfg →
    nstate_wf s →
    {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s }}}
      r @! (go.PointerType raft.raft) @! "Step" #m
    {{{ (err : error.t) s', RET #err;
        "Hphys" ∷ own_raft_phys cfg r id s' ∗
        "%Hwf'" ∷ ⌜ nstate_wf s' ⌝ ∗
        "%Hrefines" ∷ ⌜ ∃ recv,
            (∀ m', m' ∈ recv → m' = abs_msg mtype.PreVoteResp m ents) ∧
            step cfg id (to_pstate s) recv (to_pstate s') ⌝ ∗
        "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.
  Proof.
    intros Hty Hto Hterm Hnw Hcfg Hwf.
    destruct (decide (uint.Z s.(nstate.term) < uint.Z m.(raftpb.Message.Term')))
      as [Hgt|Hle].
    { exact (G.wp_Step_MsgPreVoteResp_gt cfg r id s m ents Hty Hto Hterm Hgt Hnw Hcfg Hwf). }
    destruct (decide (uint.Z m.(raftpb.Message.Term') < uint.Z s.(nstate.term)))
      as [Hlt|Hnlt].
    { exact (L.wp_Step_MsgPreVoteResp_lt cfg r id s m ents Hty Hterm Hlt Hwf). }
    assert (Heq : m.(raftpb.Message.Term') = s.(nstate.term)) by word.
    exact (E.wp_Step_MsgPreVoteResp_eq cfg r id s m ents Hty Hto Hterm Heq Hnw Hcfg Hwf).
  Qed.

End branches.

End StepMsgPreVoteResp.
