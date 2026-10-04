Require Export New.proof.go_etcd_io.raft.election_proof.inv_memstorage.

(** [ms.LastIndex()] ([storage.go:211]): the lock, [callStats]'s counter,
    the helper, the unlock.  Stated *exactly* as [is_Storage]'s [HLastIndex]
    asks of the method (same return values, [err = nil], same value), on
    [own_MemoryStorage] -- the one predicate for a [MemoryStorage] -- so that
    [is_Storage_with (own_MemoryStorage ms)] is a rearrangement of the five
    public methods' specs ([inv_memstorage.v]). *)
Definition wp_MemoryStorage__LastIndex_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (ms : loc) (prev : raft.entryID.t) (ents : list raftpb.Entry.t)
    (ss : raft.entryID.t),
  {{{ is_pkg_init raft ∗ "Hms" ∷ own_MemoryStorage ms prev ents ss }}}
    ms @! (go.PointerType raft.MemoryStorage) @! "LastIndex" #()
  {{{ (li : w64), RET (#li, #interface.nil);
      ⌜ (uint.Z li = uint.Z prev.(raft.entryID.index')
                     + Z.of_nat (length ents))%Z ⌝ ∗
      own_MemoryStorage ms prev ents ss }}}.

Module Type MEMORYSTORAGE__PUBLIC_LASTINDEX.
  Parameter wp_MemoryStorage__LastIndex : wp_MemoryStorage__LastIndex_body.
  Arguments wp_MemoryStorage__LastIndex {_ _ _ _ _ _ _ _}.
End MEMORYSTORAGE__PUBLIC_LASTINDEX.
