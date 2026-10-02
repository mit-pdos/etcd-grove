Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__handleAppendEntries.

(** * [stepFollower], for the message types in scope

    [stepFollowerⁱᵐᵖˡ] (new/code/go_etcd_io/raft/v3.v:4717; raft.go:1705)
    is a type switch over [m.Type] with arms for [MsgProp], [MsgApp],
    [MsgHeartbeat], [MsgSnap], [MsgTransferLeader], [MsgForgetLeader],
    [MsgTimeoutNow], [MsgReadIndex] and [MsgReadIndexResp], then
    [return nil].  Specified here for three types:

    - [MsgVoteResp]: no arm; nothing read or written, [nil].
    - [MsgProp]: [r.lead == None] → [Infof] and [return ErrProposalDropped],
      state unchanged.  Otherwise [r.disableProposalForwarding] is read
      (a second drop, dead under scope), then [m.To = r.lead; r.send(m)]:
      [send_ok]'s [MsgProp] clause (e) -- [Term] stays [0], [From] is
      stamped [id] -- so the outbox grows by
      [abs_msg_from mtype.Propose (m with To := lead) id 0 ents], which is
      [step_prop_forward]'s message.  **DEFERRED**: [own_raft_phys] does
      not pin [disableProposalForwarding] and [inv_raft_phys.v] has no load
      lemma for it, so the forwarding arm cannot be stepped yet; the
      premise [m.Type = MsgProp → s.lead = 0] below keeps the spec to the
      leaderless arm until it can.  The result relation already states the
      forwarding arm, and the premises it will need are already here.
    - [MsgApp]: [r.electionElapsed = 0] (not tracked), [r.lead = m.From],
      then [handleAppendEntries] ([handle_app_result] at
      [s <| lead := m.From |>]); [nil].
    - [MsgHeartbeat]: to be added with [handleHeartbeat]'s spec (a fourth
      branch of [follower_step_result], next to [MsgApp]'s).

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
    (m : raftpb.Message.t) (ents : list raftpb.Entry.t) (dropped : bool)
    (s' : nstate.t) : Prop :=
  if decide (m.(raftpb.Message.Type') = MsgVoteResp) then dropped = false ∧ s' = s
  else if decide (m.(raftpb.Message.Type') = MsgProp) then
    if decide (s.(nstate.lead) = W64 0) then dropped = true ∧ s' = s
    else dropped = false ∧ s' = send_msgs s [prop_forward id s.(nstate.lead) m ents]
  else if decide (m.(raftpb.Message.Type') = MsgApp) then
    dropped = false ∧
    handle_app_result id (s <| nstate.lead := m.(raftpb.Message.From') |>) m ents s'
  (* MsgHeartbeat: [dropped = false ∧ handle_heartbeat_result …], once
     [handleHeartbeat] has a spec *)
  else False.

(** Premises, by type:
    - [MsgProp]: [From = 0] and [Term = 0] (a local proposal; [send]
      takes the first and its [MsgProp] clause the second) and
      [lead ≠ id] ([send]'s self-addressed [Panicf]) -- for the forwarding
      arm; and, until that arm is proved, [lead = 0] (see above);
    - [MsgApp]: [handleAppendEntries]'s premises, at [s] ([lead] does not
      enter them);
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
    (ents : list raftpb.Entry.t),
  (m.(raftpb.Message.Type') = MsgVoteResp ∨ m.(raftpb.Message.Type') = MsgProp ∨
   m.(raftpb.Message.Type') = MsgApp) →
  (m.(raftpb.Message.Type') = MsgProp →
     m.(raftpb.Message.From') = W64 0 ∧ m.(raftpb.Message.Term') = W64 0 ∧
     s.(nstate.lead) ≠ id ∧
     (* DEFERRED: the forwarding arm; see the header *)
     s.(nstate.lead) = W64 0) →
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
  {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s ∗
      "Hents" ∷ (⌜ m.(raftpb.Message.Type') = MsgApp ∨ m.(raftpb.Message.Type') = MsgProp ⌝ -∗
                 m.(raftpb.Message.Entries') ↦*□ ents ∗
                 own_slice_cap raftpb.Entry.t m.(raftpb.Message.Entries') (DfracOwn 1)) }}}
    @! raft.stepFollower #r #m
  {{{ (err : error.t) (s' : nstate.t) (dropped : bool), RET #err;
      own_raft_phys cfg r id s' ∗
      ⌜ follower_step_result id s m ents dropped s' ⌝ ∗
      (if dropped then (global_addr raft.ErrProposalDropped) ↦□ err
       else ⌜ err = interface.nil ⌝) }}}.

Module Type STEPFOLLOWER.
  Parameter wp_stepFollower : wp_stepFollower_body.
  Arguments wp_stepFollower {_ _ _ _ _ _ _ _}.
End STEPFOLLOWER.
