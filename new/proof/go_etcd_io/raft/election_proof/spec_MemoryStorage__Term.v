Require Export New.proof.go_etcd_io.raft.election_proof.inv_memstorage.

(** [ms.Term(i)] ([storage.go:166]), stated exactly as [is_Storage]'s
    [HTerm] asks of the method: on the range the storage can answer for,
    [prev.index <= i <= prev.index + |ents|], it returns [term_at prev ents i]
    and no error.  The range premise is what makes [ErrCompacted]
    ([i < ents[0].Index]) and [ErrUnavailable] ([i - offset >= len(ents)])
    unreachable. *)
Definition wp_MemoryStorage__Term_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (ms : loc) (prev : raft.entryID.t) (ents : list raftpb.Entry.t)
    (ss : raft.entryID.t) (i0 : w64),
  {{{ is_pkg_init raft ∗ "Hms" ∷ own_MemoryStorage ms prev ents ss ∗
      ⌜ (uint.Z prev.(raft.entryID.index') ≤ uint.Z i0 ≤
         uint.Z prev.(raft.entryID.index') + Z.of_nat (length ents))%Z ⌝ }}}
    ms @! (go.PointerType raft.MemoryStorage) @! "Term" #i0
  {{{ (t : w64), RET (#t, #interface.nil);
      ⌜ term_at prev ents i0 = Some t ⌝ ∗ own_MemoryStorage ms prev ents ss }}}.

Module Type MEMORYSTORAGE__PUBLIC_TERM.
  Parameter wp_MemoryStorage__Term : wp_MemoryStorage__Term_body.
  Arguments wp_MemoryStorage__Term {_ _ _ _ _ _ _ _}.
End MEMORYSTORAGE__PUBLIC_TERM.
