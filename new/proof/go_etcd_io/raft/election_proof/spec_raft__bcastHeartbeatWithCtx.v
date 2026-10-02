Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [r.bcastHeartbeatWithCtx(ctx)] ([raft__bcastHeartbeatWithCtxⁱᵐᵖˡ],
    new/code/go_etcd_io/raft/v3.v:3293; [raft.go:726]):

      r.trk.Visit(func(id uint64, _ *tracker.Progress) {
        if id == r.id { return }
        r.sendHeartbeat(id, ctx)
      })

    One heartbeat per peer other than the leader itself, each with
    [Commit = min(Match, committed)] ([spec_raft__sendHeartbeat.v]).  The
    postcondition is what the model's [step_beat] asks of the broadcast:
    every message sent is one [heartbeat_ok] allows at the protocol reading
    of the state the call started in.  [heartbeat_ok] bounds [Commit] by
    [match_of], i.e. by [to_pstate]'s [matched], which is the [Progress]
    [Match] values only for a leader -- hence the premise [s.role =
    Leader].  That the list has exactly one heartbeat per peer is true but
    not stated: the model does not need it.  [SentCommit] moves no [Match]. *)
Definition wp_raft__bcastHeartbeatWithCtx_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (r : loc) (id : w64) (s : nstate.t) (ctx : slice.t),
  s.(nstate.role) = role.Leader →
  {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s }}}
    r @! (go.PointerType raft.raft) @! "bcastHeartbeatWithCtx" #ctx
  {{{ (ms : list msg.t) pvs, RET #();
      own_raft_phys cfg r id (send_msgs s ms <| nstate.prvals := pvs |>) ∗
      ⌜ Forall (heartbeat_ok id (to_pstate s)) ms ⌝ ∗
      ⌜ prvals_match pvs = prvals_match s.(nstate.prvals) ⌝ }}}.

Module Type RAFT__BCASTHEARTBEATWITHCTX.
  Parameter wp_raft__bcastHeartbeatWithCtx : wp_raft__bcastHeartbeatWithCtx_body.
  Arguments wp_raft__bcastHeartbeatWithCtx {_ _ _ _ _ _ _ _}.
End RAFT__BCASTHEARTBEATWITHCTX.
