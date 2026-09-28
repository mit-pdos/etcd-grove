Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [newReadOnly(option)] allocates a fresh [readOnly] object and returns
    it.  It reads and writes nothing else, so it owns nothing going in and
    hands back only the new object ([own_read_only], [inv_misc.v]).
    [reset] installs it with [own_raft_phys_readOnly], which needs the new
    object's ownership -- so the predicate can only be re-pointed at an
    object that was actually allocated.  (Until 2026-09-23 this spec
    consumed and returned the whole of [own_raft_misc], a raw piece of the
    raft struct.) *)
Definition wp_newReadOnly_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (o : raft.ReadOnlyOption.t),
  {{{ is_pkg_init raft }}}
    @! raft.newReadOnly #o
  {{{ (ro' : loc), RET #ro'; own_read_only ro' }}}.

Module Type NEWREADONLY.
  Parameter wp_newReadOnly : wp_newReadOnly_body.
  Arguments wp_newReadOnly {_ _ _ _ _ _ _ _}.
End NEWREADONLY.
