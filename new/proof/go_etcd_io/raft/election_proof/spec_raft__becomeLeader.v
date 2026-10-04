Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [becomeLeader] is [reset], the role transition, marking its own
    [Progress] replicating, and the empty entry, which [appendEntry]
    acknowledges with a self-addressed [MsgAppResp] ([become_leader],
    [defs.v]).  [id ∈ cfg] is needed because
    only voters are in the [Progress] map. *)
Definition wp_raft__becomeLeader_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64)
    (r : loc) (id : w64) (s : nstate.t),
  s.(nstate.role) ≠ prole.Follower →
  id ∈ cfg →
  {{{ is_pkg_init raft ∗ own_raft_phys cfg r id s }}}
    r @! (go.PointerType raft.raft) @! "becomeLeader" #()
  {{{ pvs, RET #(); own_raft_phys cfg r id (become_leader id s <| nstate.prvals := pvs |>) ∗
      (* [Match] is what [reset] left: [BecomeReplicate] and the
         [RecentActive] store do not move it, and [appendEntry] does not
         touch a [Progress] *)
      ⌜ prvals_match pvs = reset_matched id (log_last s.(nstate.logst)) s.(nstate.prvals) ⌝ }}}.

Module Type BECOMELEADER.
  Parameter wp_raft__becomeLeader : wp_raft__becomeLeader_body.
  Arguments wp_raft__becomeLeader {_ _ _ _ _ _ _ _}.
End BECOMELEADER.
