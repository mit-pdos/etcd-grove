(** [Step]'s [MsgHeartbeatResp] branch.  The three term cases are
    [wp_Step_Resp_gt], [wp_Step_Resp_lt] (shared with [MsgAppResp]) and
    [wp_Step_MsgHeartbeatResp_eq], each in its own file so they check in
    parallel; this lemma only picks one.  Proof structure, not
    specification: no [Module Type], no [Parameter]; only
    [proof_raft__Step.v] may [Require] this file. *)
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_Resp_gt.
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_Resp_lt.
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgHeartbeatResp_eq.

Module StepMsgHeartbeatResp (P : STEP_POSTULATES).
Import P.

Module G := StepRespGt P.
Module L := StepRespLt P.
Module E := StepMsgHeartbeatRespEq P.

Section branches.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).

Implicit Type s : nstate.t.

  (** [MsgHeartbeatResp]: dropped if stale, a step-down if from a higher
      term, otherwise [r.step(m)] -- at a leader, possibly a [sendAppend].
      The empty [Context] (no read-index requests in scope) keeps
      [stepLeader] out of the read-only code; [From ≠ id] rules out
      [send]'s self-addressed [Panicf]. *)
  Lemma wp_Step_MsgHeartbeatResp r id s (m : raftpb.Message.t) (ents : list raftpb.Entry.t) :
    m.(raftpb.Message.Type') = MsgHeartbeatResp →
    m.(raftpb.Message.To') = id →
    m.(raftpb.Message.Term') ≠ W64 0 →
    m.(raftpb.Message.From') ≠ W64 0 →
    m.(raftpb.Message.From') ≠ id →
    id ∈ cfg →
    nstate_wf s →
    {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s ∗
        "#Hents" ∷ m.(raftpb.Message.Entries') ↦*□ ents ∗
        "#Hctx0" ∷ m.(raftpb.Message.Context') ↦*□ ([] : list w8) }}}
      r @! (go.PointerType raft.raft) @! "Step" #m
    {{{ (err : error.t) s', RET #err;
        "Hphys" ∷ own_raft_phys cfg r id s' ∗
        "%Hwf'" ∷ ⌜ nstate_wf s' ⌝ ∗
        "%Hrefines" ∷ ⌜ ∃ recv,
            (∀ m', m' ∈ recv → m' = abs_msg mtype.HeartbeatResp m ents) ∧
            step cfg id (to_pstate s) recv (to_pstate s') ⌝ ∗
        "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.
  Proof.
    intros Hty Hto Hterm Hfnz Hfid Hcfg Hwf.
    iIntros (Φ) "(#Hinit & Hphys & _ & #Hctx0) HΦ".
    destruct (decide (uint.Z s.(nstate.term) < uint.Z m.(raftpb.Message.Term')))
      as [Hgt|Hle].
    { iApply (G.wp_Step_Resp_gt cfg r id s m ents mtype.HeartbeatResp
                (or_intror (conj Hty eq_refl)) Hto Hterm Hgt Hwf
                with "[$Hinit $Hphys] HΦ"). }
    destruct (decide (uint.Z m.(raftpb.Message.Term') < uint.Z s.(nstate.term)))
      as [Hlt|Hnlt].
    { iApply (L.wp_Step_Resp_lt cfg r id s m ents mtype.HeartbeatResp
                (or_intror Hty) Hterm Hlt Hwf
                with "[$Hinit $Hphys] HΦ"). }
    assert (Hteq : m.(raftpb.Message.Term') = s.(nstate.term)) by word.
    iApply (E.wp_Step_MsgHeartbeatResp_eq cfg r id s m ents
              Hty Hto Hterm Hteq Hfnz Hfid Hcfg Hwf
              with "[$Hinit $Hphys $Hctx0] HΦ").
  Qed.

End branches.

End StepMsgHeartbeatResp.
