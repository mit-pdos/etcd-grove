(** [Step]'s [MsgPreVote] branch (2026-10-04), combining the three term
    cases, each in its own file so that they check in parallel.  Proof
    structure, not specification: no [Module Type], no [Parameter]; only
    [proof_raft__Step.v] may [Require] this file. *)
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgPreVote_gt.
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgPreVote_eq.
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgPreVote_lt.

Module StepMsgPreVote (P : STEP_POSTULATES).
Import P.

Module G := StepMsgPreVoteGt P.
Module E := StepMsgPreVoteEq P.
Module L := StepMsgPreVoteLt P.

Section branches.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).

Implicit Type s : nstate.t.

  (** [MsgPreVote]: answered with a [MsgPreVoteResp], whatever the term;
      the node's own state never changes (no step-down, no vote recorded).
      The protocol step is one [step_send_free], consuming nothing. *)
  Lemma wp_Step_MsgPreVote r id s (m : raftpb.Message.t) :
    m.(raftpb.Message.Type') = MsgPreVote →
    m.(raftpb.Message.To') = id →
    m.(raftpb.Message.Term') ≠ W64 0 →
    m.(raftpb.Message.From') ≠ W64 0 →
    nstate_wf s →
    (s.(nstate.term) = W64 0 →
     plog_up_to_date s.(nstate.logst).(logstate.prev)
       (s.(nstate.logst).(logstate.sents) ++ s.(nstate.logst).(logstate.uents))
       (raft.entryID.mk m.(raftpb.Message.LogTerm') m.(raftpb.Message.Index')) = true) →
    {{{ is_pkg_init raft ∗
        "Hphys" ∷ own_raft_phys cfg r id s ∗
        "#Hctx" ∷ (∃ ctx, m.(raftpb.Message.Context') ↦*□ ctx ∗
                          ⌜ ctx ≠ campaignTransfer ⌝)
    }}}
      r @! (go.PointerType raft.raft) @! "Step" #m
    {{{ (err : error.t) s', RET #err;
        "Hphys" ∷ own_raft_phys cfg r id s' ∗
        "%Hwf'" ∷ ⌜ nstate_wf s' ⌝ ∗
        "%Hrefines" ∷ ⌜ step cfg id (to_pstate s) [] (to_pstate s') ⌝ ∗
        "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.
  Proof.
    intros Hty Hto Hterm Hfnz Hwf Hutd0.
    destruct (decide (uint.Z s.(nstate.term) < uint.Z m.(raftpb.Message.Term')))
      as [Hgt|Hle].
    { exact (G.wp_Step_MsgPreVote_gt cfg r id s m Hty Hto Hterm Hfnz Hgt Hwf Hutd0). }
    iIntros (Φ) "(#Hinit & Hphys & _) HΦ".
    destruct (decide (uint.Z m.(raftpb.Message.Term') < uint.Z s.(nstate.term)))
      as [Hlt|Hnlt].
    - iApply (L.wp_Step_MsgPreVote_lt cfg r id s m Hty Hto Hterm Hfnz Hlt Hwf
                with "[$Hinit $Hphys] HΦ").
    - assert (Heq : m.(raftpb.Message.Term') = s.(nstate.term)) by word.
      iApply (E.wp_Step_MsgPreVote_eq cfg r id s m Hty Hto Hterm Hfnz Heq Hwf
                with "[$Hinit $Hphys] HΦ").
  Qed.

End branches.

End StepMsgPreVote.
