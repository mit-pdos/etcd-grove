Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [newLogWithSize] builds the log over a [Storage]: everything is stable,
    the unstable suffix is empty and starts at [LastIndex()+1], and
    [committed = applied = FirstIndex()-1], the compaction boundary.

    Two premises are about the storage's *contents* and are not in
    [is_Storage]: that the stored entries carry contiguous indices after
    [prev] ([log_indices_ok]), and that none is a configuration change.
    The first is true of any correct [Storage] (and of [MemoryStorage]) but
    [own_Storage] is abstract, so a client has to supply it.  The second is
    the development's no-reconfiguration scope ([HnoConfChange],
    [inv_raftlog.v]) and is **false of a freshly bootstrapped etcd node**,
    whose storage holds the [EntryConfChange]s [Bootstrap] wrote
    (notes/STATUS.md, "What still needs fixing"). *)
Definition wp_newLogWithSize_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (st : raft.Storage.t) (lg : raft.Logger.t) (maxSize : w64)
    (prev : raft.entryID.t) (ents : list raftpb.Entry.t),
  log_indices_ok prev ents →
  Forall (λ e, e.(raftpb.Entry.Type') = EntryNormal) ents →
  {{{ is_pkg_init raft ∗ is_Storage st ∗ own_Storage st prev ents }}}
    @! raft.newLogWithSize #st #lg #maxSize
  {{{ (l : loc), RET #l;
      own_raftLog l (logstate.mk prev ents []
                       prev.(raft.entryID.index') prev.(raft.entryID.index') None) }}}.

Module Type NEWLOGWITHSIZE.
  Parameter wp_newLogWithSize : wp_newLogWithSize_body.
  Arguments wp_newLogWithSize {_ _ _ _ _ _ _ _}.
End NEWLOGWITHSIZE.
