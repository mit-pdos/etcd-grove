Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

Section defs.
Context {ext : ffi_syntax}.

(** What [Config.validate] checks, as a proposition over the [Config].
    Each conjunct is exactly the condition Go tests before one of its
    [return errors.New(...)]s, except [Logger ≠ nil]: Go substitutes the
    package default logger ([getLogger]) for a nil one, and taking the
    logger as given keeps the default logger out of the trust base. *)
Definition config_valid (cv : raft.Config.t) : Prop :=
  cv.(raft.Config.ID') ≠ W64 0 ∧
  cv.(raft.Config.ID') ≠ W64 18446744073709551615 ∧
  cv.(raft.Config.ID') ≠ W64 18446744073709551614 ∧
  (0 < sint.Z cv.(raft.Config.HeartbeatTick')
     < sint.Z cv.(raft.Config.ElectionTick'))%Z ∧
  cv.(raft.Config.Storage') ≠ interface.nil ∧
  (0 < sint.Z cv.(raft.Config.MaxInflightMsgs'))%Z ∧
  (cv.(raft.Config.MaxInflightBytes') = W64 0 ∨
   uint.Z cv.(raft.Config.MaxSizePerMsg')
     ≤ uint.Z cv.(raft.Config.MaxInflightBytes'))%Z ∧
  cv.(raft.Config.Logger') ≠ interface.nil ∧
  (cv.(raft.Config.ReadOnlyOption') = W64 0 ∨
   cv.(raft.Config.CheckQuorum') = true).

(** [validate] writes defaults into up to four fields
    ([MaxUncommittedEntriesSize], [MaxCommittedSizePerReady],
    [MaxInflightBytes], and [Logger] when nil).  The postcondition says
    only which fields it preserves -- the ones [newRaft] reads and a proof
    needs to know -- and not what the defaults are. *)
Definition config_preserved (cv cv' : raft.Config.t) : Prop :=
  cv'.(raft.Config.ID') = cv.(raft.Config.ID') ∧
  cv'.(raft.Config.ElectionTick') = cv.(raft.Config.ElectionTick') ∧
  cv'.(raft.Config.HeartbeatTick') = cv.(raft.Config.HeartbeatTick') ∧
  cv'.(raft.Config.Storage') = cv.(raft.Config.Storage') ∧
  cv'.(raft.Config.Applied') = cv.(raft.Config.Applied') ∧
  cv'.(raft.Config.MaxInflightMsgs') = cv.(raft.Config.MaxInflightMsgs') ∧
  cv'.(raft.Config.CheckQuorum') = cv.(raft.Config.CheckQuorum') ∧
  cv'.(raft.Config.PreVote') = cv.(raft.Config.PreVote') ∧
  cv'.(raft.Config.Logger') = cv.(raft.Config.Logger').

End defs.

Definition wp_Config__validate_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (c : loc) (cv : raft.Config.t),
  config_valid cv →
  {{{ is_pkg_init raft ∗ c ↦ cv }}}
    c @! (go.PointerType raft.Config) @! "validate" #()
  {{{ (cv' : raft.Config.t), RET #interface.nil;
      c ↦ cv' ∗ ⌜ config_preserved cv cv' ⌝ }}}.

Module Type CONFIG__VALIDATE.
  Parameter wp_Config__validate : wp_Config__validate_body.
  Arguments wp_Config__validate {_ _ _ _ _ _ _ _}.
End CONFIG__VALIDATE.
