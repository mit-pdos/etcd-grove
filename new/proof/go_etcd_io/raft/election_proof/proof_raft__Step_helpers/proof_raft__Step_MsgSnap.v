(** [Step]'s [MsgSnap] branch (2026-10-02): the term preamble, then the type
    switch's default arm [r.step(m)].  Three term cases, each in its own
    file; this lemma only picks one:

    - [m.Term > r.Term] ([proof_raft__Step_MsgSnap_gt.v]): the preamble's
      [becomeFollower(m.Term, m.From)] ([step_higher_term] at [abs_snap]),
      then [stepFollower]'s [MsgSnap] arm on the stepped-down state;
    - [m.Term < r.Term] ([_lt.v]): logged and dropped ([step_refl]);
    - [m.Term = r.Term] ([_eq.v]): [r.step(m)] by role -- the follower's and
      the candidate's arms adopt the sender and run [handleSnapshot]; a
      leader is excluded by the premise the dispatch derives from
      [is_leader_unique].

    [handleSnapshot]'s three exits refine [step_snap_stale],
    [step_snap_fastfwd] and [step_snap_restore] ([step_handle_snap]).

    Proof structure, not specification: no [Module Type], no [Parameter];
    only [proof_raft__Step.v], or another file in this directory, may
    [Require] it. *)
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgSnap_gt.
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgSnap_lt.
Require Export New.proof.go_etcd_io.raft.election_proof.proof_raft__Step_helpers.proof_raft__Step_MsgSnap_eq.

Module StepMsgSnap (P : STEP_POSTULATES).
Import P.

Module G := StepMsgSnapGt P.
Module L := StepMsgSnapLt P.
Module E := StepMsgSnapEq P.

Section branches.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).

Implicit Type s : nstate.t.

  Lemma wp_Step_MsgSnap r id s (m : raftpb.Message.t)
      (sv : raftpb.Snapshot.t) (voters : list w64) :
    m.(raftpb.Message.Type') = MsgSnap →
    m.(raftpb.Message.To') = id →
    m.(raftpb.Message.Term') ≠ W64 0 →
    m.(raftpb.Message.From') ≠ W64 0 →
    m.(raftpb.Message.From') ≠ id →
    id ∈ cfg →
    nstate_wf s →
    (* the snapshot's [ConfState] is [cfg]'s voters, zero-free, no learners
       or joint configuration; its index below [2^61] ([Step]'s ["Hsnap"]) *)
    snap_scope cfg sv voters →
    (* protocol facts the dispatch derives from the ghost state: at the
       current term the receiver is not a leader ([is_leader_unique]), and a
       follower's tally is empty ([follower_votes_ok]) *)
    (m.(raftpb.Message.Term') = s.(nstate.term) → s.(nstate.role) ≠ role.Leader) →
    (s.(nstate.role) = role.Follower → s.(nstate.votes) = ∅) →
    {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s ∗
        "#Hsv" ∷ m.(raftpb.Message.Snapshot') ↦□ sv ∗
        "#Hvs" ∷ sv.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.ConfState')
                   .(raftpb.ConfState.Voters') ↦*□ voters }}}
      r @! (go.PointerType raft.raft) @! "Step" #m
    {{{ (err : error.t) s', RET #err;
        "Hphys" ∷ own_raft_phys cfg r id s' ∗
        "%Hwf'" ∷ ⌜ nstate_wf s' ⌝ ∗
        "%Hrefines" ∷ ⌜ ∃ recv,
            (∀ m', m' ∈ recv → m' = abs_snap m sv voters) ∧
            step cfg id (to_pstate s) recv (to_pstate s') ⌝ ∗
        "%Herr" ∷ ⌜ err = interface.nil ⌝ }}}.
  Proof.
    intros Hty Hto Hterm Hfnz Hfid Hcfg Hwf Hscope Hnl Hvotes.
    destruct (decide (uint.Z s.(nstate.term) < uint.Z m.(raftpb.Message.Term')))
      as [Hgt|Hle].
    - exact (G.wp_Step_MsgSnap_gt cfg r id s m sv voters Hty Hto Hterm Hfnz Hfid Hcfg Hwf Hscope Hgt).
    - destruct (decide (uint.Z m.(raftpb.Message.Term') < uint.Z s.(nstate.term)))
        as [Hlt|Hnlt].
      + iIntros (Φ) "(#Hinit & Hphys & _) HΦ".
        iApply (L.wp_Step_MsgSnap_lt cfg r id s m sv voters Hty Hto Hterm Hwf Hlt
                 with "[$Hinit $Hphys] HΦ").
      + assert (Hteq : m.(raftpb.Message.Term') = s.(nstate.term)) by word.
        exact (E.wp_Step_MsgSnap_eq cfg r id s m sv voters Hty Hto Hterm Hfnz Hfid Hcfg Hwf
                 Hscope Hteq (Hnl Hteq) Hvotes).
  Qed.

End branches.

End StepMsgSnap.
