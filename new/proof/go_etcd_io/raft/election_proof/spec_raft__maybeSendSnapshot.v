Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [r.maybeSendSnapshot(to, pr)] -- the fallback when the log no longer has
    what a peer needs ([raft__maybeSendSnapshotⁱᵐᵖˡ],
    new/code/go_etcd_io/raft/v3.v:3166).

      if !pr.RecentActive        { Debugf; return false }
      snapshot, err := r.raftLog.snapshot()
      if err == ErrSnapshotTemporarilyUnavailable { Debugf; return false }
      if err != nil              { panic(err) }
      if IsEmptySnap(snapshot)   { panic("need non-empty snapshot") }
      Debugf; pr.BecomeSnapshot(sindex); Debugf
      r.send(pb.Message{To: to, Type: MsgSnap, Snapshot: snapshot})
      return true

    **The model sees nothing.**  [MsgSnap] has no [mtype_of], so it falls
    under the third clause of [send_ok] ([spec_raft__send.v]) and
    contributes nothing to the abstract outbox -- which is why the
    postcondition is at the *same* [s].  [Term] is unset in the literal and
    [to ≠ id] (the only caller, [maybeSendAppend], is reached from
    [bcastAppend], which skips the leader itself), so that clause applies.

    [pr] moves to [StateSnapshot], which is why the [Progress] comes back
    existentially quantified rather than at its old value.

    **Resources.**  The struct arrives whole, as [own_raft_phys], and [pr]
    is *named* rather than owned: it is the peer's [Progress] in the
    progress map [s.(nstate.progress)], and the proof borrows it out of the
    tracker itself and puts it back before the [send].  From 2026-09-21 to
    2026-09-22 this was stated on a variant predicate, [own_raft_notrk] --
    the struct with the tracker cut out -- plus [own_progress pr], because
    [own_raft_phys cfg r id s ∗ own_progress pr] is contradictory at the
    only call site (the [Progress] is already inside [own_tracker];
    notes/false-statements.md, 2026-09-21).  Recording the progress map in
    [nstate.t] removes the need for the variant: the caller hands [pr] back
    to the tracker before the call and borrows it again after, at the same
    key.

    Reaching [Storage.Snapshot] is what forced the [HSnapshot] triple into
    [is_Storage] ([inv_storage.v]).  This branch is genuinely reachable from
    [own_raft_phys]: nothing in [own_progress] bounds [pr.Next] against the
    log, so [r.raftLog.term(pr.Next-1)] may legitimately return
    [ErrCompacted]. *)
Definition wp_raft__maybeSendSnapshot_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (r : loc) (id : w64) (s : nstate.t) (to : w64) (pr : loc),
  to ≠ id →
  s.(nstate.progress) !! to = Some pr →
  (* it reads the log ([raftLog.snapshot], [firstIndex]) *)
  s.(nstate.lent) = None →
  {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_phys cfg r id s }}}
    r @! (go.PointerType raft.raft) @! "maybeSendSnapshot" #to #pr
  {{{ (b : bool), RET #b; own_raft_phys cfg r id s }}}.

Module Type RAFT__MAYBESENDSNAPSHOT.
  Parameter wp_raft__maybeSendSnapshot : wp_raft__maybeSendSnapshot_body.
  Arguments wp_raft__maybeSendSnapshot {_ _ _ _ _ _ _ _}.
End RAFT__MAYBESENDSNAPSHOT.
