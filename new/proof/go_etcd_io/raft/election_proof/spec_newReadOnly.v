Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** The old queue is dropped and a fresh one installed.  The lemma *consumes*
    [own_raft_misc] at [ro] and returns it at [ro'], which is what [reset]
    does.  Note it is *not* the shape [own_raft_misc rv -∗ own_raft_misc rv'],
    which would let any caller re-index the predicate to a queue it never
    allocated: this one is tied to an actual allocation, and [ro'] comes out
    of the call. *)
Definition wp_newReadOnly_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (o : raft.ReadOnlyOption.t) rs ro pri,
  {{{ is_pkg_init raft ∗ own_raft_misc rs ro pri }}}
    @! raft.newReadOnly #o
  {{{ (ro' : loc), RET #ro'; own_raft_misc rs ro' pri }}}.

Module Type NEWREADONLY.
  Parameter wp_newReadOnly : wp_newReadOnly_body.
  Arguments wp_newReadOnly {_ _ _ _ _ _ _ _}.
End NEWREADONLY.
