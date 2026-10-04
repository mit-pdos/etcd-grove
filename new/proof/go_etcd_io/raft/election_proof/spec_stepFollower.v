Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__handleAppendEntries.
Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__handleHeartbeat.
Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__handleSnapshot.

(** For a caller of [stepFollower]/[stepCandidate] with a message that is
    not a [MsgSnap]: the ["Hsnap"] premise's wand, discharged by its
    antecedent's falsity -- some hypothesis [m.Type = c] (or a disjunction
    of such) with [c] not [MsgSnap]. *)
Ltac step_no_snap :=
  iIntros "%"; exfalso;
  match goal with
  | Hs : raftpb.Message.Type' ?m = MsgSnap |- _ =>
    first
    [ match goal with
      | H : raftpb.Message.Type' m = ?c |- _ =>
          tryif unify c MsgSnap then fail
          else (rewrite H in Hs; revert Hs; w32_ne)
      end
    | match goal with
      | H : raftpb.Message.Type' m = _ ∨ _ |- _ =>
          let Hd := fresh "Hd" in
          destruct H as [Hd|[Hd|Hd]]; rewrite Hd in Hs; revert Hs; w32_ne
      end ]
  end.

(** * [stepFollower], for the message types in scope

    [stepFollowerⁱᵐᵖˡ] (new/code/go_etcd_io/raft/v3.v:4717; raft.go:1705)
    is a type switch over [m.Type] with arms for [MsgProp], [MsgApp],
    [MsgHeartbeat], [MsgSnap], [MsgTransferLeader], [MsgForgetLeader],
    [MsgTimeoutNow], [MsgReadIndex] and [MsgReadIndexResp], then
    [return nil].  Specified for every type [Step] dispatches to it:

    - [MsgVoteResp], [MsgBeat], [MsgAppResp], [MsgHeartbeatResp], and
      (since 2026-10-04) [MsgPreVoteResp]: no arm; nothing read or
      written, [nil].
    - [MsgProp]: [r.lead == None] → [Infof] and [return ErrProposalDropped],
      state unchanged.  Otherwise [r.disableProposalForwarding] is read --
      [false], by [own_raft_phys]'s [HpropForward] scope conjunct, so the
      second drop is dead -- then [m.To = r.lead; r.send(m)]: [send_ok]'s
      [MsgProp] clause (e) -- [Term] stays [0], [From] is stamped [id] --
      so the outbox grows by [abs_msg_from mtype.Propose (m with To :=
      lead) id 0 ents], which is [prop_forward] below and
      [step_prop_forward]'s message.  (Until 2026-10-02 the forwarding arm
      was deferred behind a premise [lead = 0].)
    - [MsgApp]: [r.electionElapsed = 0] (not tracked), [r.lead = m.From],
      then [handleAppendEntries] ([handle_app_result] at
      [s <| lead := m.From |>]); [nil].
    - [MsgHeartbeat]: the same two stores, then [handleHeartbeat]
      ([heartbeat_result] at [s <| lead := m.From |>]); [nil].
    - [MsgSnap] (since 2026-10-02): the same two stores, then
      [handleSnapshot] ([handle_snap_result] at [s <| lead := m.From |>],
      for the snapshot [sv] that [m.Snapshot] points to); [nil].

    The role is never read: the triple holds for any [s].  (A caller
    reaching it through [r.step] knows [s.role = Follower] from
    [nstate_wf].) *)

(** The forwarded proposal as [send] queues it: [m] with [To := lead],
    [From := id] (stamped; [m.From = 0]), [Term = 0] (not stamped for
    [MsgProp]), the rest [m]'s.  Field for field what [step_prop_forward]
    sends ([msg.mk mtype.Propose id s.lead (W64 0) m.reject m.index
    m.logterm m.commit m.rejecthint m.entries]). *)
Definition prop_forward (id lead : w64) (m : raftpb.Message.t)
    (ents : list raftpb.Entry.t) : msg.t :=
  msg.mk mtype.Propose id lead (W64 0) m.(raftpb.Message.Reject')
    m.(raftpb.Message.Index') m.(raftpb.Message.LogTerm')
    m.(raftpb.Message.Commit') m.(raftpb.Message.RejectHint') ents.

(** What [stepFollower] does with [m], by type.  [dropped] is whether it
    returned [ErrProposalDropped] (the postcondition then says [err] is
    that global's value; otherwise [err = nil]). *)
Definition follower_step_result {ext : ffi_syntax} (id : w64) (s : nstate.t)
    (m : raftpb.Message.t) (ents : list raftpb.Entry.t) (sv : raftpb.Snapshot.t)
    (dropped : bool) (s' : nstate.t) : Prop :=
  if decide (m.(raftpb.Message.Type') = MsgVoteResp) then dropped = false ∧ s' = s
  else if decide (m.(raftpb.Message.Type') = MsgProp) then
    if decide (s.(nstate.lead) = W64 0) then dropped = true ∧ s' = s
    else dropped = false ∧ s' = send_msgs s [prop_forward id s.(nstate.lead) m ents]
  else if decide (m.(raftpb.Message.Type') = MsgApp) then
    dropped = false ∧
    handle_app_result id (s <| nstate.lead := m.(raftpb.Message.From') |>) m ents s'
  else if decide (m.(raftpb.Message.Type') = MsgHeartbeat) then
    dropped = false ∧
    s' = heartbeat_result id (s <| nstate.lead := m.(raftpb.Message.From') |>) m
  else if decide (m.(raftpb.Message.Type') = MsgBeat ∨
                  m.(raftpb.Message.Type') = MsgAppResp ∨
                  m.(raftpb.Message.Type') = MsgHeartbeatResp) then
    dropped = false ∧ s' = s
  else if decide (m.(raftpb.Message.Type') = MsgSnap) then
    dropped = false ∧
    handle_snap_result id (s <| nstate.lead := m.(raftpb.Message.From') |>) m sv s'
  else if decide (m.(raftpb.Message.Type') = MsgPreVoteResp) then dropped = false ∧ s' = s
  else False.

(** Premises, by type:
    - [MsgProp]: [From = 0] and [Term = 0] (a local proposal; [send]
      takes the first and its [MsgProp] clause the second) and
      [lead ≠ id] ([send]'s self-addressed [Panicf]) -- for the forwarding
      arm;
    - [MsgApp]: [handleAppendEntries]'s premises, at [s] ([lead] does not
      enter them);
    - [MsgHeartbeat]: [handleHeartbeat]'s two -- [m.Commit] within the log
      ([commitTo]'s [Panicf]; the protocol fact [heartbeat_commit_le_last])
      and [m.From ≠ id] ([send]'s self-addressed [Panicf]);
    - [Hents]: the [Entries] slice for the two types that use it --
      read-only for [send]/[maybeAppend], with its capacity for
      [maybeAppend] (it may adopt the slice).  For [MsgVoteResp] the wand
      is discharged by the type. *)
Definition wp_stepFollower_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64)
    (r : loc) (id : w64) (s : nstate.t) (m : raftpb.Message.t)
    (ents : list raftpb.Entry.t) (sv : raftpb.Snapshot.t) (voters : list w64),
  (m.(raftpb.Message.Type') = MsgVoteResp ∨ m.(raftpb.Message.Type') = MsgProp ∨
   m.(raftpb.Message.Type') = MsgApp ∨ m.(raftpb.Message.Type') = MsgHeartbeat ∨
   (m.(raftpb.Message.Type') = MsgBeat ∨ m.(raftpb.Message.Type') = MsgAppResp ∨
    m.(raftpb.Message.Type') = MsgHeartbeatResp) ∨
   m.(raftpb.Message.Type') = MsgSnap ∨ m.(raftpb.Message.Type') = MsgPreVoteResp) →
  (m.(raftpb.Message.Type') = MsgProp →
     m.(raftpb.Message.From') = W64 0 ∧ m.(raftpb.Message.Term') = W64 0 ∧
     s.(nstate.lead) ≠ id) →
  (m.(raftpb.Message.Type') = MsgApp →
     plog_wf (raft.entryID.mk m.(raftpb.Message.LogTerm') m.(raftpb.Message.Index')) ents ∧
     (uint.Z m.(raftpb.Message.Index') + Z.of_nat (length ents) + 1 < 2^64)%Z ∧
     Forall (λ e, e.(raftpb.Entry.Type') = EntryNormal) ents ∧
     (let ls := s.(nstate.logst) in
      let es := ls.(logstate.sents) ++ ls.(logstate.uents) in
      uint.Z ls.(logstate.committed) ≤ uint.Z m.(raftpb.Message.Index') →
      plog_matches ls.(logstate.prev) es
        (raft.entryID.mk m.(raftpb.Message.LogTerm') m.(raftpb.Message.Index')) →
      plog_find_conflict ls.(logstate.prev) es ents = W64 0 ∨
      uint.Z ls.(logstate.committed) < uint.Z (plog_find_conflict ls.(logstate.prev) es ents))%Z) →
  (m.(raftpb.Message.Type') = MsgHeartbeat →
     (uint.Z m.(raftpb.Message.Commit')
        ≤ plog_last_index_Z s.(nstate.logst).(logstate.prev)
            (s.(nstate.logst).(logstate.sents) ++ s.(nstate.logst).(logstate.uents)))%Z ∧
     m.(raftpb.Message.From') ≠ id) →
  {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s ∗
      "Hsnap" ∷ (⌜ m.(raftpb.Message.Type') = MsgSnap ⌝ -∗
                 ⌜ snap_scope cfg sv voters ∧ s.(nstate.role) = prole.Follower ∧
                   s.(nstate.votes) = ∅ ∧ id ∈ cfg ⌝ ∗
                 m.(raftpb.Message.Snapshot') ↦□ sv ∗
                 sv.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.ConfState')
                   .(raftpb.ConfState.Voters') ↦*□ voters) ∗
      "Hents" ∷ (⌜ m.(raftpb.Message.Type') = MsgApp ∨ m.(raftpb.Message.Type') = MsgProp ⌝ -∗
                 m.(raftpb.Message.Entries') ↦*□ ents ∗
                 own_slice_cap raftpb.Entry.t m.(raftpb.Message.Entries') (DfracOwn 1)) }}}
    @! raft.stepFollower #r #m
  {{{ (err : error.t) (s' : nstate.t) (dropped : bool), RET #err;
      own_raft_phys cfg r id s' ∗
      ⌜ follower_step_result id s m ents sv dropped s' ⌝ ∗
      (if dropped then (global_addr raft.ErrProposalDropped) ↦□ err
       else ⌜ err = interface.nil ⌝) }}}.

Module Type STEPFOLLOWER.
  Parameter wp_stepFollower : wp_stepFollower_body.
  Arguments wp_stepFollower {_ _ _ _ _ _ _ _}.
End STEPFOLLOWER.
