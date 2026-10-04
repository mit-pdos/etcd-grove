Require Export New.proof.go_etcd_io.raft.election_proof.inv_memstorage.

(** [ms.firstIndex()] ([storage.go:236]): [ents[0].Index + 1].
    Called with the lock held, so it is stated on [memstorage_fields], the
    lock's contents, rather than on [own_MemoryStorage].  The bound is a
    premise: the sum cannot wrap. *)
Definition wp_MemoryStorage__firstIndex_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (ms : loc) (prev : raft.entryID.t) (ents : list raftpb.Entry.t)
    (ss : raft.entryID.t),
  (uint.Z prev.(raft.entryID.index') + Z.of_nat (length ents) < 2^61)%Z →
  {{{ is_pkg_init raft ∗ "Hf" ∷ memstorage_fields ms prev ents ss }}}
    ms @! (go.PointerType raft.MemoryStorage) @! "firstIndex" #()
  {{{ (fi : w64), RET #fi;
      ⌜ (uint.Z fi = uint.Z prev.(raft.entryID.index') + 1)%Z ⌝ ∗
      memstorage_fields ms prev ents ss }}}.

Module Type MEMORYSTORAGE__FIRSTINDEX.
  Parameter wp_MemoryStorage__firstIndex : wp_MemoryStorage__firstIndex_body.
  Arguments wp_MemoryStorage__firstIndex {_ _ _ _ _ _ _ _}.
End MEMORYSTORAGE__FIRSTINDEX.
