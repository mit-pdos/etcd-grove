Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [l.snapshot()] -- the snapshot the log can offer a lagging peer
    ([raftLog__snapshotⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3.v:864):

      if l.unstable.snapshot != nil { return *l.unstable.snapshot, nil }
      return l.storage.Snapshot()

    Either the distinguished [ErrSnapshotTemporarilyUnavailable] -- whose
    points-to the caller passes in, since the comparison in
    [maybeSendSnapshot] is against the package-level variable, not against
    a claim about [errors.New] -- or a [nil] error and a snapshot whose
    metadata [(Term, Index)] is

    - non-zero ([IsEmptySnap]'s test, so [maybeSendSnapshot]'s [panic] is
      dead),
    - at or below [committed], and an entry id of the log: the log has
      [Term] at [Index] ([plog_term_at], possibly as its base) -- since
      2026-10-03, for [snap_ok] ([protocol.v]),

    with its [ConfState.Voters] slice read-only, for good (since
    2026-10-03, so that the [MsgSnap] built from it is abstracted from the
    heap, [msg_abs]).

    Two sources.  A pending snapshot ([logstate.snap]) is returned by value
    from [*l.unstable.snapshot]: it *is* the log's base ([log_store_ok]),
    at or below [committed] by [own_raftLog]; its voters are [own_snap]'s.
    Otherwise [Storage.Snapshot()]: [is_Storage]'s [HSnapshot] says the
    snapshot is the storage's own, [ss], and [own_raftLog]'s
    [stored_snap_ok] relates [ss] to the log and the commit index.

    The log comes back at the same state, like [raftLog.firstIndex]: the
    one caller, [raft.maybeSendSnapshot], calls both on the same log. *)
Definition wp_raftLog__snapshot_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (ls : logstate.t) (esu : interface.t),
  {{{ is_pkg_init raft ∗ "Hlog" ∷ own_raftLog l ls ∗
      "#Hesu" ∷ (global_addr raft.ErrSnapshotTemporarilyUnavailable) ↦□ esu }}}
    l @! (go.PointerType raft.raftLog) @! "snapshot" #()
  {{{ (snap : raftpb.Snapshot.t) (err : interface.t), RET (#snap, #err);
      own_raftLog l ls ∗
      (⌜ err = esu ⌝ ∨
       (⌜ err = interface.nil ∧
          snap.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.Index') ≠ W64 0 ∧
          (uint.Z snap.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.Index')
             ≤ uint.Z ls.(logstate.committed))%Z ∧
          plog_term_at ls.(logstate.prev) (ls.(logstate.sents) ++ ls.(logstate.uents))
            snap.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.Index')
          = Some snap.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.Term') ⌝ ∗
        ∃ (voters : list w64),
          snap.(raftpb.Snapshot.Metadata').(raftpb.SnapshotMetadata.ConfState')
            .(raftpb.ConfState.Voters') ↦*□ voters)) }}}.

Module Type RAFTLOG__SNAPSHOT.
  Parameter wp_raftLog__snapshot : wp_raftLog__snapshot_body.
  Arguments wp_raftLog__snapshot {_ _ _ _ _ _ _ _}.
End RAFTLOG__SNAPSHOT.
