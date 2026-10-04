Require Export New.proof.go_etcd_io.raft.election_proof.inv_memstorage.

(** [ms.Snapshot()] ([storage.go:244]): returns [ms.snapshot] by value, and
    [nil].  Stated exactly as [is_Storage]'s [HSnapshot] asks of the method,
    including the premise about [ErrSnapshotTemporarilyUnavailable] and the
    error *disjunction* -- [MemoryStorage] only ever takes the second
    disjunct ([nil], the stored snapshot).  The snapshot's metadata is the
    storage's [ss] ([snap_id]); it is non-empty because [own_MemoryStorage]
    says [ss.index <> 0] (a finding about the contract: a [MemoryStorage] with
    no snapshot returns an empty one, which [is_Storage] excludes); and its
    [ConfState.Voters] slice is the read-only one [own_MemoryStorage] holds. *)
Definition wp_MemoryStorage__Snapshot_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (ms : loc) (prev : raft.entryID.t) (ents : list raftpb.Entry.t)
    (ss : raft.entryID.t) (esu : interface.t),
  {{{ is_pkg_init raft ∗ "Hms" ∷ own_MemoryStorage ms prev ents ss ∗
      (global_addr raft.ErrSnapshotTemporarilyUnavailable) ↦□ esu }}}
    ms @! (go.PointerType raft.MemoryStorage) @! "Snapshot" #()
  {{{ (snap : raftpb.Snapshot.t) (err : interface.t), RET (#snap, #err);
      own_MemoryStorage ms prev ents ss ∗
      (⌜ err = esu ⌝ ∨
       (⌜ err = interface.nil ∧ snap_id snap = ss ∧
          snap.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.Index')
            ≠ W64 0 ⌝ ∗
        ∃ (voters : list w64),
          snap.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.ConfState')
            .(raftpb.ConfState.Voters') ↦*□ voters)) }}}.

Module Type MEMORYSTORAGE__PUBLIC_SNAPSHOT.
  Parameter wp_MemoryStorage__Snapshot : wp_MemoryStorage__Snapshot_body.
  Arguments wp_MemoryStorage__Snapshot {_ _ _ _ _ _ _ _}.
End MEMORYSTORAGE__PUBLIC_SNAPSHOT.
