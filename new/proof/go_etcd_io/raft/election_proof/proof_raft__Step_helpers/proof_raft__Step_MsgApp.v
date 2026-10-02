(** [Step]'s [MsgApp] branch: the term preamble, then the type switch's
    default arm [r.step(m)].  Three term cases, each in its own file so that
    they check in parallel; this lemma only picks one:

    - [m.Term > r.Term] ([proof_raft__Step_MsgApp_gt.v]): the preamble's
      [becomeFollower(m.Term, m.From)] ([step_higher_term], which adopts the
      sender for a [from_leader] type), then [stepFollower]'s arm on the
      stepped-down state;
    - [m.Term < r.Term] ([_lt.v]): with [checkQuorum] and [preVote] off the
      message is logged and dropped ([step_refl], nothing received);
    - [m.Term = r.Term] ([_eq.v]): [r.step(m)] by role -- the follower's
      and the candidate's arms adopt the sender and run the handler, the
      leader's does nothing.

    Proof structure, not specification: no [Module Type], no [Parameter];
    only [proof_raft__Step.v], or another file in this directory, may
    [Require] it. *)
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgApp_gt.
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgApp_lt.
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgApp_eq.

Module StepMsgApp (P : STEP_POSTULATES).
Import P.

Module G := StepMsgAppGt P.
Module L := StepMsgAppLt P.
Module E := StepMsgAppEq P.

Section branches.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).

Implicit Type s : nstate.t.

  Lemma wp_Step_MsgApp r id s (m : raftpb.Message.t) (ents : list raftpb.Entry.t) :
    m.(raftpb.Message.Type') = MsgApp →
    m.(raftpb.Message.To') = id →
    m.(raftpb.Message.Term') ≠ W64 0 →
    m.(raftpb.Message.From') ≠ W64 0 →
    m.(raftpb.Message.From') ≠ id →
    id ∈ cfg →
    nstate_wf s →
    (* protocol facts the dispatch derives from the ghost state (app_recv_wf, app_no_conflict_below_commit) *)
    plog_wf (raft.entryID.mk m.(raftpb.Message.LogTerm') m.(raftpb.Message.Index')) ents →
    (uint.Z m.(raftpb.Message.Index') + Z.of_nat (length ents) + 1 < 2^64)%Z →
    Forall (λ e, e.(raftpb.Entry.Type') = EntryNormal) ents →
    (let ls := s.(nstate.logst) in
     let es := ls.(logstate.sents) ++ ls.(logstate.uents) in
     (uint.Z ls.(logstate.committed) ≤ uint.Z m.(raftpb.Message.Index'))%Z →
     plog_matches ls.(logstate.prev) es
       (raft.entryID.mk m.(raftpb.Message.LogTerm') m.(raftpb.Message.Index')) →
     plog_find_conflict ls.(logstate.prev) es ents = W64 0 ∨
     (uint.Z ls.(logstate.committed) < uint.Z (plog_find_conflict ls.(logstate.prev) es ents))%Z) →
    (* ADDED (not in the brief): a follower's vote tally is empty.  The
       follower case of [m.Term = r.Term] refines [step_app_accept] /
       [step_heartbeat] etc., whose [padopt_leader] clears [votes]; the Go
       code's [r.lead = m.From] does not touch [r.trk.Votes], so the two
       agree only when the tally already is empty.  Every way of becoming a
       follower ([becomeFollower]'s [reset], [newRaft]) leaves it empty and a
       follower never records a vote, but neither [nstate_wf] nor the ghost
       state says so. *)
    (s.(nstate.role) = role.Follower → s.(nstate.votes) = ∅) →
    {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s ∗
        "#Hents" ∷ m.(raftpb.Message.Entries') ↦*□ ents ∗
        "Hcap" ∷ own_slice_cap raftpb.Entry.t m.(raftpb.Message.Entries') (DfracOwn 1) }}}
      r @! (go.PointerType raft.raft) @! "Step" #m
    {{{ (err : error.t) s', RET #err;
        "Hphys" ∷ own_raft_phys cfg r id s' ∗
        "%Hwf'" ∷ ⌜ nstate_wf s' ⌝ ∗
        "%Hrefines" ∷ ⌜ ∃ recv,
            (∀ m', m' ∈ recv → m' = abs_msg mtype.App m ents) ∧
            step cfg id (to_pstate s) recv (to_pstate s') ⌝ ∗
        "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.
  Proof.
    intros Hty Hto Hterm Hfnz Hfid Hcfg Hwf Hpwf Hnw Hnorm Hconf Hvotes.
    destruct (decide (uint.Z s.(nstate.term) < uint.Z m.(raftpb.Message.Term')))
      as [Hgt|Hle].
    - exact (G.wp_Step_MsgApp_gt cfg r id s m ents Hty Hto Hterm Hfnz Hfid Hcfg Hwf Hpwf Hnw Hnorm Hconf Hgt).
    - destruct (decide (uint.Z m.(raftpb.Message.Term') < uint.Z s.(nstate.term)))
        as [Hlt|Hnlt].
      + exact (L.wp_Step_MsgApp_lt cfg r id s m ents Hty Hto Hterm Hfnz Hfid Hcfg Hwf Hpwf Hnw Hnorm Hconf Hlt).
      + assert (Hteq : m.(raftpb.Message.Term') = s.(nstate.term)) by word.
        exact (E.wp_Step_MsgApp_eq cfg r id s m ents Hty Hto Hterm Hfnz Hfid Hcfg Hwf Hpwf Hnw Hnorm Hconf Hteq Hvotes).
  Qed.

End branches.

End StepMsgApp.
