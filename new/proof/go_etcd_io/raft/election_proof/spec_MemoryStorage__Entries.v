Require Export New.proof.go_etcd_io.raft.election_proof.inv_memstorage.

(** [ms.Entries(lo, hi, maxSize)] ([storage.go:131]), stated exactly as
    [is_Storage]'s [HEntries] asks of the method.  The range premise
    [prev.index + 1 <= lo < hi <= prev.index + |ents| + 1] makes all three
    error paths unreachable: [lo <= ents[0].Index] ([ErrCompacted]),
    [hi > lastIndex + 1] (the [Panicf]) and [len(ents) == 1]
    ([ErrUnavailable]).  The result is [limitSize] of the sub-slice
    [ents[lo-offset:hi-offset]], re-sliced with [cap = len]; the entries are
    returned read-only and for good, which [own_MemoryStorage] can allow
    because it holds [ms.ents] read-only itself. *)
Definition wp_MemoryStorage__Entries_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (ms : loc) (prev : raft.entryID.t) (ents : list raftpb.Entry.t)
    (ss : raft.entryID.t) (lo hi maxSize : w64),
  {{{ is_pkg_init raft ∗ "Hms" ∷ own_MemoryStorage ms prev ents ss ∗
      ⌜ (uint.Z prev.(raft.entryID.index') + 1 ≤ uint.Z lo ∧ uint.Z lo < uint.Z hi ∧
         uint.Z hi ≤ uint.Z prev.(raft.entryID.index') + Z.of_nat (length ents) + 1)%Z ⌝ }}}
    ms @! (go.PointerType raft.MemoryStorage) @! "Entries" #lo #hi #maxSize
  {{{ (s : slice.t) (es : list raftpb.Entry.t),
      RET (#s, #interface.nil);
      s ↦*□ es ∗
      ⌜ es ≠ [] ∧
        (Z.of_nat (length es) ≤ uint.Z hi - uint.Z lo)%Z ∧
        (∀ e, e ∈ es → e ∈ take (Z.to_nat (uint.Z hi - uint.Z prev.(raft.entryID.index') - 1)) ents) ∧
        s.(slice.cap) = s.(slice.len) ∧
        es `prefix_of` drop (Z.to_nat (uint.Z lo - uint.Z prev.(raft.entryID.index') - 1))
                         (take (Z.to_nat (uint.Z hi - uint.Z prev.(raft.entryID.index') - 1)) ents) ⌝ ∗
      own_MemoryStorage ms prev ents ss }}}.

Module Type MEMORYSTORAGE__PUBLIC_ENTRIES.
  Parameter wp_MemoryStorage__Entries : wp_MemoryStorage__Entries_body.
  Arguments wp_MemoryStorage__Entries {_ _ _ _ _ _ _ _}.
End MEMORYSTORAGE__PUBLIC_ENTRIES.
