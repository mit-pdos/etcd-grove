Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [l.snapshot()] -- the snapshot the log can offer a lagging peer
    ([raftLog__snapshotⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:864):

      if l.unstable.snapshot != nil { return *l.unstable.snapshot, nil }
      return l.storage.Snapshot()

    [own_raftLog]'s [Hnosnap] says the unstable snapshot is always [nil]
    on this path (no snapshot is ever received -- see [inv_raftlog.v]), so
    the first branch is dead and the result is exactly what the
    client-supplied [Storage] returns.  The postcondition is therefore
    [is_Storage]'s [HSnapshot] clause verbatim ([inv_storage.v]): either the
    distinguished [ErrSnapshotTemporarilyUnavailable] -- whose points-to the
    caller passes in, since the comparison in [maybeSendSnapshot] is against
    the package-level variable, not against a claim about [errors.New] -- or
    success with a snapshot whose [Metadata.Index] is non-zero.

    The log comes back at the same state, like [raftLog.firstIndex]: the
    one caller, [raft.maybeSendSnapshot], calls both on the same log. *)
Definition wp_raftLog__snapshot_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (ls : logstate.t) (esu : interface.t),
  ls.(logstate.page) = None →
  {{{ is_pkg_init raft ∗ "Hlog" ∷ own_raftLog l ls ∗
      "#Hesu" ∷ (global_addr raft.ErrSnapshotTemporarilyUnavailable) ↦□ esu }}}
    l @! (go.PointerType raft.raftLog) @! "snapshot" #()
  {{{ (snap : raftpb.Snapshot.t) (err : interface.t), RET (#snap, #err);
      own_raftLog l ls ∗
      ⌜ err = esu ∨
        (err = interface.nil ∧
         snap.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.Index')
           ≠ W64 0) ⌝ }}}.

Module Type RAFTLOG__SNAPSHOT.
  Parameter wp_raftLog__snapshot : wp_raftLog__snapshot_body.
  Arguments wp_raftLog__snapshot {_ _ _ _ _ _ _ _}.
End RAFTLOG__SNAPSHOT.
