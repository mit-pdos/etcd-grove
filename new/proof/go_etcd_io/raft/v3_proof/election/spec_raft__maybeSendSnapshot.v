Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

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

    **The tracker is not in the precondition** (changed 2026-09-21).  It
    used to be [own_raft_phys cfg r id s ∗ own_progress pr], and those two
    are **contradictory at the only call site**: [own_raft_phys] contains
    [own_tracker], which contains [[∗ map] p ∈ prs, own_progress p] with
    [dom prs = cfg], and [maybeSendAppend] calls this with
    [pr = prs !! to] for a voter [to], so the second [own_progress pr] is
    the same exclusive [pr ↦ pv].  The triple was true and [Qed], and
    uncallable.  (notes/false-statements.md, 2026-09-21.)  So the raft
    struct arrives as [own_raft_notrk] -- everything but the tracker, with
    the tracker *value* [tv] pinned as a parameter -- and the caller keeps
    the tracker, minus the one [Progress] it lends here.  The log stays in
    (this function calls [raftLog.snapshot] and [raftLog.firstIndex]).

    [f] is the [r.step] parameter of [own_raft_phys_at]; this function does
    not touch the field, so it is carried through unchanged.

    Reaching [Storage.Snapshot] is what forced the [HSnapshot] triple into
    [is_Storage] ([inv_storage.v]).  This branch is genuinely reachable from
    [own_raft_phys]: nothing in [own_progress] bounds [pr.Next] against the
    log, so [r.raftLog.term(pr.Next-1)] may legitimately return
    [ErrCompacted]. *)
Definition wp_raft__maybeSendSnapshot_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (r : loc) (id : w64) (s : nstate.t) (f : func.t)
    (tv : tracker.ProgressTracker.t) (to : w64) (pr : loc),
  to ≠ id →
  {{{ is_pkg_init raft ∗ "Hphys" ∷ own_raft_notrk r id s f tv ∗
      "Hpr" ∷ own_progress pr }}}
    r @! (go.PointerType raft.raft) @! "maybeSendSnapshot" #to #pr
  {{{ (b : bool), RET #b; own_raft_notrk r id s f tv ∗ own_progress pr }}}.

Module Type RAFT__MAYBESENDSNAPSHOT.
  Parameter wp_raft__maybeSendSnapshot : wp_raft__maybeSendSnapshot_body.
  Arguments wp_raft__maybeSendSnapshot {_ _ _ _ _ _ _ _}.
End RAFT__MAYBESENDSNAPSHOT.
