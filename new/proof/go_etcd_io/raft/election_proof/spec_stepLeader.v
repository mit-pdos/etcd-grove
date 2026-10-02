Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.
Require Export New.proof.go_etcd_io.raft.election_proof.spec_raft__maybeCommit.

(** * [stepLeader(r, m)] on the message types a leader handles in phase 1

    [stepLeaderⁱᵐᵖˡ] ([new/code/go_etcd_io/raft/v3.v:4167]; [raft.go:1262])
    is *two* type switches with a progress-map lookup in between:

      switch m.Type {                 // MsgBeat, MsgCheckQuorum, MsgProp,
      ...                             // MsgReadIndex, MsgForgetLeader
      }
      pr := r.trk.Progress[m.From]
      if pr == nil { r.logger.Debugf(...); return nil }
      switch m.Type {                 // MsgAppResp, MsgHeartbeatResp,
      ...                             // MsgSnapStatus, MsgUnreachable,
      }                               // MsgTransferLeader
      return nil

    This spec covers four types.  ([MsgProp] is a later wave; the rest are
    out of scope.)

    - [MsgVoteResp] is in neither switch: nothing changes.
    - [MsgBeat]: [r.bcastHeartbeat()] ([spec_raft__bcastHeartbeat.v]) --
      heartbeats [heartbeat_ok] allows, which is the model's [step_beat].
    - [MsgHeartbeatResp]: [pr.RecentActive], [pr.MsgAppFlowPaused] written;
      [sendAppend(m.From)] when the peer is behind or probing; then
      [if r.readOnly.option != ReadOnlySafe || len(m.Context) == 0 { return
      nil }].  The read-only code after it is skipped because a heartbeat
      response in scope carries no context: [bcastHeartbeat] sends [nil]
      ([heartbeatCtx], no read requests) and [handleHeartbeat] echoes it --
      the premise [Hctx] below.  So: [repl_sends] growth, no [Match] moved
      (the model's [step_send_apps], or [step_refl]).
    - [MsgAppResp], the replication path ([raft.go:1371-1565]):
      * no [Progress] for the sender: unchanged;
      * rejected: [MaybeDecrTo], perhaps [BecomeProbe], perhaps
        [sendAppend(m.From)] -- [Next] moves, [Match] does not;
        [repl_sends] growth;
      * accepted: [MaybeUpdate(m.Index)] raises the sender's [Match] to
        [max Match m.Index] (the model's [step_app_resp]); then
        [BecomeReplicate]/[BecomeProbe]/[Inflights.FreeLE] as the
        [Progress] state says (no [Match] moves); [maybeCommit()] may
        advance [committed] to an [N] with [commit_ok] **at the updated
        [Match] map** ([step_commit]); then [bcastAppend] (after a commit)
        or [sendAppend] (for [CanBumpCommit]) and the
        [for r.maybeSendAppend(m.From, false) {}] loop ([step_send_apps],
        judged after the commit).  [releasePendingReadIndexMessages] is a
        no-op under the scope.  [sendTimeoutNow] is dead: it needs
        [m.From = r.leadTransferee], which is [0] ([own_raft_phys]'s
        [HnoTransfer]), and [m.From ≠ 0] is a premise.

    Each case is stated so that [Step] can build its [step] witness as a
    chain of model rules; [leader_step_result] below is that statement. *)

(** [MsgBeat = 1] ([raftpb.v:76]); [defs.v] names the types the model
    describes, and [MsgBeat] is local. *)
Definition MsgBeat : w32 := W32 1.

(** [MsgAppResp] accepted from [from] at [index]: [s'] is [s] with the
    sender's [Match] raised as [MaybeUpdate] raises it (the [Progress]
    values are otherwise unconstrained: [pvs]), [committed] at [c] --
    unchanged, or a [commit_ok] index judged against the raised [Match]
    map -- and the outbox grown by [ms], which [repl_sends] allows after
    the commit. *)
Definition app_resp_accepted {ext : ffi_syntax} (cfg : gset w64) (id : w64) (s : nstate.t)
    (from index : w64) (s' : nstate.t) : Prop :=
  ∃ (x : w64) pvs (c : w64) (ms : list msg.t),
    prvals_match s.(nstate.prvals) !! from = Some x ∧
    prvals_match pvs =
      <[from := if decide (uint.Z x < uint.Z index) then index else x]>
        (prvals_match s.(nstate.prvals)) ∧
    (c = s.(nstate.logst).(logstate.committed) ∨
     commit_ok cfg (to_pstate (s <| nstate.prvals := pvs |>)) c) ∧
    repl_sends id
      (s <| nstate.logst := s.(nstate.logst) <| logstate.committed := c |> |>) ms ∧
    s' = send_msgs
           (s <| nstate.logst := s.(nstate.logst) <| logstate.committed := c |> |>) ms
           <| nstate.prvals := pvs |>.

(** What [stepLeader] does with [m], by type.  The disjuncts are exclusive
    on [m.Type]. *)
Definition leader_step_result {ext : ffi_syntax} (cfg : gset w64) (id : w64) (s : nstate.t)
    (m : raftpb.Message.t) (s' : nstate.t) : Prop :=
  (m.(raftpb.Message.Type') = MsgVoteResp ∧ s' = s) ∨
  (m.(raftpb.Message.Type') = MsgBeat ∧
   ∃ ms pvs, s' = send_msgs s ms <| nstate.prvals := pvs |> ∧
             Forall (heartbeat_ok id (to_pstate s)) ms ∧
             prvals_match pvs = prvals_match s.(nstate.prvals)) ∨
  (m.(raftpb.Message.Type') = MsgHeartbeatResp ∧
   ∃ ms pvs, s' = send_msgs s ms <| nstate.prvals := pvs |> ∧
             repl_sends id s ms ∧
             prvals_match pvs = prvals_match s.(nstate.prvals)) ∨
  (m.(raftpb.Message.Type') = MsgAppResp ∧
   ((m.(raftpb.Message.From') ∉ dom s.(nstate.progress) ∧ s' = s) ∨
    (m.(raftpb.Message.From') ∈ dom s.(nstate.progress) ∧
     m.(raftpb.Message.Reject') = true ∧
     ∃ ms pvs, s' = send_msgs s ms <| nstate.prvals := pvs |> ∧
               repl_sends id s ms ∧
               prvals_match pvs = prvals_match s.(nstate.prvals)) ∨
    (m.(raftpb.Message.From') ∈ dom s.(nstate.progress) ∧
     m.(raftpb.Message.Reject') = false ∧
     app_resp_accepted cfg id s m.(raftpb.Message.From') m.(raftpb.Message.Index') s'))).

(** Premises, each tied to the exit it rules out:
    - [s.role = Leader]: [r.step = stepLeader] means it ([nstate_wf]), and
      [to_pstate]'s [matched] is [Match] only for a leader;
    - [id ∈ cfg]: [maybeCommit]'s quorum ([spec_raft__maybeCommit.v]);
    - [m.From ≠ 0] on [MsgAppResp]: [sendTimeoutNow] is dead
      ([leadTransferee = 0]);
    - [m.From ≠ id] where [sendAppend(m.From)] can run: [send]'s
      self-addressed [Panicf].  An accepting [MsgAppResp] may come from the
      node itself ([appendEntry]'s self-acknowledgement): the code guards
      every send to [m.From] by [r.id != m.From] there;
    - [Hctx]: a [MsgHeartbeatResp] carries an empty [Context] (for any
      other type the wand is trivial: [iIntros (?); exfalso]). *)
Definition wp_stepLeader_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64)
    (r : loc) (id : w64) (s : nstate.t) (m : raftpb.Message.t),
  (m.(raftpb.Message.Type') = MsgVoteResp ∨ m.(raftpb.Message.Type') = MsgBeat ∨
   m.(raftpb.Message.Type') = MsgHeartbeatResp ∨ m.(raftpb.Message.Type') = MsgAppResp) →
  s.(nstate.role) = role.Leader →
  id ∈ cfg →
  (m.(raftpb.Message.Type') = MsgAppResp → m.(raftpb.Message.From') ≠ W64 0) →
  (m.(raftpb.Message.Type') = MsgHeartbeatResp ∨
   (m.(raftpb.Message.Type') = MsgAppResp ∧ m.(raftpb.Message.Reject') = true) →
   m.(raftpb.Message.From') ≠ id) →
  {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s ∗
      "Hctx" ∷ (⌜ m.(raftpb.Message.Type') = MsgHeartbeatResp ⌝ -∗
                 m.(raftpb.Message.Context') ↦*□ ([] : list w8)) }}}
    @! raft.stepLeader #r #m
  {{{ (err : error.t) (s' : nstate.t), RET #err;
      own_raft_phys cfg r id s' ∗ ⌜ err = interface.nil ⌝ ∗
      ⌜ leader_step_result cfg id s m s' ⌝ }}}.

Module Type STEPLEADER.
  Parameter wp_stepLeader : wp_stepLeader_body.
  Arguments wp_stepLeader {_ _ _ _ _ _ _ _}.
End STEPLEADER.
