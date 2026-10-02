Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [r.bcastHeartbeat()] ([raft__bcastHeartbeatⁱᵐᵖˡ],
    new/code/go_etcd_io/raft/v3.v:3285; [raft.go:722]):

      r.bcastHeartbeatWithCtx(r.readOnly.heartbeatCtx())

    [heartbeatCtx] returns [nil] under the scope (no read requests;
    [spec_readOnly__heartbeatCtx.v]), and reading it leaves the [readOnly]
    object as it was; the rest is [bcastHeartbeatWithCtx]'s spec.  This is
    what [stepLeader] does on a [MsgBeat], and the postcondition is the
    model's [step_beat]. *)
Definition wp_raft__bcastHeartbeat_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (r : loc) (id : w64) (s : nstate.t),
  s.(nstate.role) = role.Leader →
  {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s }}}
    r @! (go.PointerType raft.raft) @! "bcastHeartbeat" #()
  {{{ (ms : list msg.t) pvs, RET #();
      own_raft_phys cfg r id (send_msgs s ms <| nstate.prvals := pvs |>) ∗
      ⌜ Forall (heartbeat_ok id (to_pstate s)) ms ⌝ ∗
      ⌜ prvals_match pvs = prvals_match s.(nstate.prvals) ⌝ }}}.

Module Type RAFT__BCASTHEARTBEAT.
  Parameter wp_raft__bcastHeartbeat : wp_raft__bcastHeartbeat_body.
  Arguments wp_raft__bcastHeartbeat {_ _ _ _ _ _ _ _}.
End RAFT__BCASTHEARTBEAT.
