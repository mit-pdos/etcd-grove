(** One term case of [Step]'s [MsgVote] branch, in its own file so that it
    checks in parallel with the other -- see [proof_raft__Step_MsgVote.v],
    which combines the two, and [notes/decisions.md] (2026-09-17).  Proof
    structure, not specification: no [Module Type], no [Parameter]; only
    [proof_raft__Step_MsgVote.v] may [Require] this file. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__Step_MsgVote_lt.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__Step_MsgVote_eq_novote.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__Step_MsgVote_eq_voted.

Module StepMsgVoteLe (P : STEP_POSTULATES).
Import P.

Module Lt := StepMsgVoteLt P.
Module EqNovote := StepMsgVoteEqNovote P.
Module EqVoted := StepMsgVoteEqVoted P.

Section branches.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).

Implicit Type γ : raft_election_names.
Implicit Type s : nstate.t.

  (** [MsgVote] with [m.Term ≤ r.Term]: three cases, each in its own file so
      they check in parallel; this lemma only picks one.  [m.Term < r.Term] drops
      the message; [m.Term = r.Term] answers it, and how depends on whether this
      node has already voted in the term. *)
  Lemma wp_Step_MsgVote_le r id s (m : raftpb.Message.t) :
    m.(raftpb.Message.Type') = MsgVote →
    m.(raftpb.Message.To') = id →
    m.(raftpb.Message.Term') ≠ W64 0 →
    (* [send] stamps the sender's id into [From], and node ids are nonzero *)
    m.(raftpb.Message.From') ≠ W64 0 →
    (* this file: the incoming term is not higher, so no step-down *)
    ¬ (uint.Z s.(nstate.term) < uint.Z m.(raftpb.Message.Term')) →
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
    intros Hty Hto Hterm Hfnz Hle0.
    destruct (decide (uint.Z m.(raftpb.Message.Term') < uint.Z s.(nstate.term)))
      as [Hlt|Hnlt].
    - exact (Lt.wp_Step_MsgVote_lt cfg r id s m Hty Hto Hterm Hfnz Hlt).
    - assert (Heq : m.(raftpb.Message.Term') = s.(nstate.term)) by word.
      destruct (decide (s.(nstate.vote) = W64 0)) as [Hv0|Hv0].
      + exact (EqNovote.wp_Step_MsgVote_eq_novote cfg r id s m Hty Hto Hterm Hfnz Heq Hv0).
      + exact (EqVoted.wp_Step_MsgVote_eq_voted cfg r id s m Hty Hto Hterm Hfnz Heq Hv0).
  Qed.

End branches.

End StepMsgVoteLe.
