Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [r.loadState(hs)] restores a persisted [HardState]: [raftLog.committed],
    [Term] and [Vote].  It [Panicf]s unless [hs.Commit] lies in
    [[committed, lastIndex()]], hence the premise.

    The log is **on loan** ([nstate.lent], [defs.v]): the caller holds
    [own_raftLog] at a known state, which is what lets the premise talk
    about [committed] and [lastIndex()] at all -- [own_raft_phys] alone
    quantifies the log's state away.  The one caller is [newRaft], which
    has the tracker and log on loan anyway while it builds the struct. *)
Definition wp_raft__loadState_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (r : loc) (id : w64) (s : nstate.t)
    (tv : tracker.ProgressTracker.t) (ls : logstate.t) (hs : raftpb.HardState.t),
  s.(nstate.lent) = Some tv →
  ls.(logstate.page) = None →
  (uint.Z ls.(logstate.committed) ≤ uint.Z hs.(raftpb.HardState.Commit')
     ≤ uint.Z ls.(logstate.prev).(raft.entryID.index')
       + Z.of_nat (length ls.(logstate.sents))
       + Z.of_nat (length ls.(logstate.uents)))%Z →
  {{{ is_pkg_init raft ∗ own_raft_phys cfg r id s ∗
      own_raftLog s.(nstate.log) ls }}}
    r @! (go.PointerType raft.raft) @! "loadState" #hs
  {{{ RET #();
      own_raft_phys cfg r id
        (s <| nstate.term := hs.(raftpb.HardState.Term') |>
           <| nstate.vote := hs.(raftpb.HardState.Vote') |>) ∗
      own_raftLog s.(nstate.log)
        (ls <| logstate.committed := hs.(raftpb.HardState.Commit') |>) }}}.

Module Type RAFT__LOADSTATE.
  Parameter wp_raft__loadState : wp_raft__loadState_body.
  Arguments wp_raft__loadState {_ _ _ _ _ _ _ _}.
End RAFT__LOADSTATE.
