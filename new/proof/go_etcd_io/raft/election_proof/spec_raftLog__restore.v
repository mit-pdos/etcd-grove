Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [l.restore(s)] ([log.go:464], [raftLog__restoreⁱᵐᵖˡ]):

        l.logger.Infof("log [%s] starts to restore snapshot [index: %d, term: %d]", ...)
        l.committed = s.Metadata.Index
        l.unstable.restore(s)

    The log becomes the snapshot: [log_restore] ([defs.v]) -- [prev] the
    snapshot's id, no entries, [committed] its index, [applied] unchanged,
    the snapshot pending.  The [Storage] is not touched; it is shadowed
    while the snapshot is pending ([log_store_ok], [inv_raftlog.v]).

    Premises, both for [own_raftLog] at the new state rather than for the
    body (which cannot fail): the snapshot is above the commit index
    ([raft.restore]'s first test), so [applied <= committed] survives and
    the index is non-zero; and its index is below [2^61], [log_store_ok]'s
    bound for a pending snapshot (a transport premise of [Step]). *)
Definition wp_raftLog__restore_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (ls : logstate.t) (sv : raftpb.Snapshot.t),
  (uint.Z ls.(logstate.committed) < uint.Z (snap_id sv).(raft.entryID.index'))%Z →
  (uint.Z (snap_id sv).(raft.entryID.index') < 2^61)%Z →
  {{{ is_pkg_init raft ∗ "Hlog" ∷ own_raftLog l ls }}}
    l @! (go.PointerType raft.raftLog) @! "restore" #sv
  {{{ RET #(); own_raftLog l (log_restore ls (snap_id sv)) }}}.

Module Type RAFTLOG__RESTORE.
  Parameter wp_raftLog__restore : wp_raftLog__restore_body.
  Arguments wp_raftLog__restore {_ _ _ _ _ _ _ _}.
End RAFTLOG__RESTORE.
