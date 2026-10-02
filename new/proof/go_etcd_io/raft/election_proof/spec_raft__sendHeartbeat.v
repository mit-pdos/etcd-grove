Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [r.sendHeartbeat(to, ctx)] ([raft__sendHeartbeatⁱᵐᵖˡ],
    new/code/go_etcd_io/raft/v3.v:3240; [raft.go:692]):

      pr := r.trk.Progress[to]
      commit := min(pr.Match, r.raftLog.committed)
      r.send(pb.Message{To: to, Type: pb.MsgHeartbeat, Commit: commit, Context: ctx})
      pr.SentCommit(commit)

    [to ∈ cfg] makes the lookup hit (otherwise [pr] is nil and [pr.Match]
    faults); [to ≠ id] rules out [send]'s self-addressed [Panicf].

    The outbox grows by one [Heartbeat] to [to] at the current term whose
    [Commit] is [min(Match of to, committed)]; the two bounds the model's
    [heartbeat_ok] asks for are exposed as pure facts, against
    [prvals_match] (what [to_pstate]'s [matched] is for a leader) and the
    log's [committed].  [ctx] is not owned: it is only copied into
    [Context], which the abstraction ignores.  [SentCommit] writes
    [sentCommit] and nothing else, so [Match] is untouched. *)
Definition wp_raft__sendHeartbeat_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (r : loc) (id : w64) (s : nstate.t) (to : w64) (ctx : slice.t),
  to ≠ id →
  to ∈ cfg →
  {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s }}}
    r @! (go.PointerType raft.raft) @! "sendHeartbeat" #to #ctx
  {{{ (c : w64) pvs, RET #();
      own_raft_phys cfg r id
        (send_msgs s [msg.mk mtype.Heartbeat id to s.(nstate.term) false
                        (W64 0) (W64 0) c (W64 0) []]
           <| nstate.prvals := pvs |>) ∗
      ⌜ uint.Z c ≤ uint.Z s.(nstate.logst).(logstate.committed) ⌝ ∗
      ⌜ uint.Z c ≤ uint.Z (default (W64 0) (prvals_match s.(nstate.prvals) !! to)) ⌝ ∗
      ⌜ prvals_match pvs = prvals_match s.(nstate.prvals) ⌝ }}}.

Module Type RAFT__SENDHEARTBEAT.
  Parameter wp_raft__sendHeartbeat : wp_raft__sendHeartbeat_body.
  Arguments wp_raft__sendHeartbeat {_ _ _ _ _ _ _ _}.
End RAFT__SENDHEARTBEAT.
