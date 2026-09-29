Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [r.loadState(hs)] restores a persisted [HardState]: [raftLog.committed],
    [Term] and [Vote].  It [Panicf]s unless [hs.Commit] lies in
    [[committed, lastIndex()]], hence the premise -- stated on the log's
    state [s.logst], which [nstate.t] records.

    [nstate.lent] is not constrained: the one caller, [newRaft], calls it
    with the tracker still on loan, and [loadState] does not touch the
    tracker.  (Until 2026-09-25 the *log* had to be on loan too, because
    [own_raft_phys] did not record its state.) *)
Definition wp_raft__loadState_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (r : loc) (id : w64) (s : nstate.t) (hs : raftpb.HardState.t),
  s.(nstate.logst).(logstate.page) = None →
  (uint.Z s.(nstate.logst).(logstate.committed) ≤ uint.Z hs.(raftpb.HardState.Commit')
     ≤ uint.Z (log_last s.(nstate.logst)))%Z →
  {{{ is_pkg_init raft ∗ own_raft_phys cfg r id s }}}
    r @! (go.PointerType raft.raft) @! "loadState" #hs
  {{{ RET #();
      own_raft_phys cfg r id
        (s <| nstate.term := hs.(raftpb.HardState.Term') |>
           <| nstate.vote := hs.(raftpb.HardState.Vote') |>
           <| nstate.logst := s.(nstate.logst)
                <| logstate.committed := hs.(raftpb.HardState.Commit') |> |>) }}}.

Module Type RAFT__LOADSTATE.
  Parameter wp_raft__loadState : wp_raft__loadState_body.
  Arguments wp_raft__loadState {_ _ _ _ _ _ _ _}.
End RAFT__LOADSTATE.
