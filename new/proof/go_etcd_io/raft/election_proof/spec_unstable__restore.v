Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [u.restore(s)] ([log_unstable.go:188], [unstable__restoreⁱᵐᵖˡ]):

        u.offset = s.Metadata.Index + 1
        u.offsetInProgress = u.offset
        u.entries = nil
        u.snapshot = &s
        u.snapshotInProgress = false

    [&s] is the address of the by-value parameter, a fresh heap cell; it
    comes back read-only as [own_snap] of the snapshot's id ([snap_id]).
    The old entries are dropped (the suffix is empty, a [nil] slice), and
    the logger is left alone. *)
Definition wp_unstable__restore_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (u : loc) (uv : raft.unstable.t) (uents : list raftpb.Entry.t)
    (sv : raftpb.Snapshot.t),
  {{{ is_pkg_init raft ∗ "Hun" ∷ own_unstable u uv uents }}}
    u @! (go.PointerType raft.unstable) @! "restore" #sv
  {{{ (uv' : raft.unstable.t), RET #();
      own_unstable u uv' [] ∗
      own_snap uv'.(raft.unstable.snapshot') (Some (snap_id sv)) ∗
      ⌜ uv'.(raft.unstable.offset')
          = word.add sv.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.Index') (W64 1) ∧
        uv'.(raft.unstable.logger') = uv.(raft.unstable.logger') ⌝ }}}.

Module Type UNSTABLE__RESTORE.
  Parameter wp_unstable__restore : wp_unstable__restore_body.
  Arguments wp_unstable__restore {_ _ _ _ _ _ _ _}.
End UNSTABLE__RESTORE.
