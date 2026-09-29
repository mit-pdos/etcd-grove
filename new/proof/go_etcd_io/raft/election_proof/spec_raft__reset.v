Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [reset term] clears the vote iff the term changes, clears [lead] and the
    vote tally, and re-initializes the non-election state; [reset_to]
    ([defs.v]) is exactly that.  [r.step] is untouched, so [becomeFollower]
    -- which assigns it *before* calling [reset] -- gets it back as it left
    it. *)
Definition wp_raft__reset_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64)
    (r : loc) (id : w64) (s : nstate.t) (term : w64),
  (* [Visit]'s closure calls [lastIndex], so the log must be whole *)
  nstate_idle s →
  {{{ is_pkg_init raft ∗ own_raft_phys cfg r id s }}}
    r @! (go.PointerType raft.raft) @! "reset" #term
  {{{ RET #(); own_raft_phys cfg r id (reset_to s term) }}}.

Module Type RESET.
  Parameter wp_raft__reset : wp_raft__reset_body.
  Arguments wp_raft__reset {_ _ _ _ _ _ _ _}.
End RESET.
