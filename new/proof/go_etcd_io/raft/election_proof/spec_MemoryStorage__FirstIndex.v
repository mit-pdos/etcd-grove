Require Export New.proof.go_etcd_io.raft.election_proof.inv_memstorage.

(** [ms.FirstIndex()] ([storage.go:230]): the lock, [callStats]'s counter,
    the helper, the unlock.  Stated *exactly* as [is_Storage]'s [HFirstIndex]
    asks of the method (same return values, [err = nil], same value), on
    [own_MemoryStorage] -- the one predicate for a [MemoryStorage] -- so that
    [is_Storage_with (own_MemoryStorage ms)] is a rearrangement of the five
    public methods' specs ([inv_memstorage.v]). *)
Definition wp_MemoryStorage__FirstIndex_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (ms : loc) (prev : raft.entryID.t) (ents : list raftpb.Entry.t)
    (ss : raft.entryID.t),
  {{{ is_pkg_init raft ∗ "Hms" ∷ own_MemoryStorage ms prev ents ss }}}
    ms @! (go.PointerType raft.MemoryStorage) @! "FirstIndex" #()
  {{{ (fi : w64), RET (#fi, #interface.nil);
      ⌜ (uint.Z fi = uint.Z prev.(raft.entryID.index') + 1)%Z ⌝ ∗
      own_MemoryStorage ms prev ents ss }}}.

Module Type MEMORYSTORAGE__PUBLIC_FIRSTINDEX.
  Parameter wp_MemoryStorage__FirstIndex : wp_MemoryStorage__FirstIndex_body.
  Arguments wp_MemoryStorage__FirstIndex {_ _ _ _ _ _ _ _}.
End MEMORYSTORAGE__PUBLIC_FIRSTINDEX.
