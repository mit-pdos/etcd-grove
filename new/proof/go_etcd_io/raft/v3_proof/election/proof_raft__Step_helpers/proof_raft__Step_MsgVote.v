(** One branch of [Step]'s proof, in its own file so that the three branches
    check in parallel under [make -j] -- each is a few minutes of [wp_auto]
    over the same 100k-node body, and in one file they ran back to back.

    This is **proof structure, not specification**: [Step] has exactly one
    spec, in [spec_raft__Step.v], and this module has no [Module Type] and no
    [Parameter].  Nothing but [proof_raft__Step.v], or another file in this
    directory, may [Require] it; see [notes/decisions.md] (2026-09-17, and
    2026-09-18 for why the helpers moved out of the top-level directory). *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__Step_helpers.proof_raft__Step_MsgVote_gt.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.proof_raft__Step_helpers.proof_raft__Step_MsgVote_le.

Module StepMsgVote (P : STEP_POSTULATES).
Import P.

Module G := StepMsgVoteGt P.
Module L := StepMsgVoteLe P.

Section branches.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).

Implicit Type γ : raft_election_names.
Implicit Type s : nstate.t.

  (** [MsgVote]: step down if the term is higher, then grant or decline.  The
      two term cases are [wp_Step_MsgVote_gt] and [wp_Step_MsgVote_le], each in
      its own file so they check in parallel; this lemma only picks one. *)
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
    destruct (decide (uint.Z s.(nstate.term) < uint.Z m.(raftpb.Message.Term')))
      as [Hgt|Hle].
    - exact (G.wp_Step_MsgVote_gt cfg r id s m Hty Hto Hterm Hfnz Hgt).
    - exact (L.wp_Step_MsgVote_le cfg r id s m Hty Hto Hterm Hfnz Hle).
  Qed.

End branches.

End StepMsgVote.
