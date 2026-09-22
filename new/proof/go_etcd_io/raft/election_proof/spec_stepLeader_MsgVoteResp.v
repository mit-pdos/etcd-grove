Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [stepLeader] on a [MsgVoteResp]: nothing observable.

    [stepLeaderⁱᵐᵖˡ] ([new/code/go_etcd_io/raft/v3.v]) is *two* type switches
    with a progress-map lookup in between:

      switch m.Type {                 // MsgBeat, MsgCheckQuorum, MsgProp,
      ...                             // MsgReadIndex, MsgForgetLeader
      }
      pr := r.trk.Progress[m.From]
      if pr == nil {
          r.logger.Debugf("%x no progress available for %x", r.id, m.From)
          return nil
      }
      switch m.Type {                 // MsgAppResp, MsgHeartbeatResp,
      ...                             // MsgSnapStatus, MsgUnreachable,
      }                               // MsgTransferLeader
      return nil

    [MsgVoteResp] appears in neither switch, so it falls off the end of both.
    The code in between reads [r.trk.Progress], [r.id] and [r.logger] and may
    log, but it writes nothing, so the raft struct -- outbox included -- is
    left exactly as it was.

    Hence the same trivial postcondition as [stepFollower]'s: state unchanged,
    [nil] error.  Note in particular that no [m.From ∈ cfg] premise is needed:
    the lookup's result is only compared against [nil], and *both* outcomes
    return [nil] without touching the state, so the proof never has to know
    whether the sender is a voter. *)
Definition wp_stepLeader_MsgVoteResp_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64)
    (r : loc) (id : w64) (s : nstate.t) (m : raftpb.Message.t),
  m.(raftpb.Message.Type') = MsgVoteResp →
  {{{ is_pkg_init raft ∗ own_raft_phys cfg r id s }}}
    @! raft.stepLeader #r #m
  {{{ (err : error.t), RET #err;
      own_raft_phys cfg r id s ∗ ⌜ err = interface.nil ⌝ }}}.

Module Type STEPLEADER.
  Parameter wp_stepLeader_MsgVoteResp : wp_stepLeader_MsgVoteResp_body.
  Arguments wp_stepLeader_MsgVoteResp {_ _ _ _ _ _ _ _}.
End STEPLEADER.
