Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [r.hasUnappliedConfChanges()]: false, since there is no
    reconfiguration.

    The tempting shortcut does not work: the generated body
    ([new/code/go_etcd_io/raft/v3.v:3732]) opens with

        if r.raftLog.applied >= r.raftLog.committed { return false }

    but [applied >= committed] is a fact about the log that nothing available
    implies, so the [scan] over [(applied, committed]] is **genuinely
    reachable** -- it is not dead under our scope.  Returning [false]
    therefore needs [own_raftLog] to say that no entry in that range has
    [Type] [EntryConfChange] or [EntryConfChangeV2], which is
    [HnoConfChange] in [own_raftLog] ([inv_raftlog.v]), together with
    [Happlied]/[Hcommitted] placing [(applied, committed]] inside the log so
    that [scan]'s bounds checks cannot panic.

    **Owns the receiver.**  The method has a pointer receiver and reads
    [r.raftLog] through it four times before anything else, so the triple
    takes [r ↦ rv] and speaks of [own_raftLog rv.(raftLog')] -- the
    [wp_ProgressTracker__Visit] rule (notes/false-statements.md).  Until
    2026-09-19 it was stated on an unrelated [l : loc] with no ownership of
    [r] at all, which asserted the safety of a load it did not own; that
    version was never proved.  [r.logger] is also read, but only on the
    [Panicf] path, which is dead. *)
Definition wp_raft__hasUnappliedConfChanges_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (r : loc) (id : w64) (s : nstate.t),
  (* it scans the log *)
  s.(nstate.lent) = None →
  {{{ is_pkg_init raft ∗ own_raft_phys cfg r id s }}}
    r @! (go.PointerType raft.raft) @! "hasUnappliedConfChanges" #()
  {{{ RET #false; own_raft_phys cfg r id s }}}.

Module Type RAFT__HASUNAPPLIEDCONFCHANGES.
  Parameter wp_raft__hasUnappliedConfChanges : wp_raft__hasUnappliedConfChanges_body.
  Arguments wp_raft__hasUnappliedConfChanges {_ _ _ _ _ _ _ _}.
End RAFT__HASUNAPPLIEDCONFCHANGES.
