Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [r.hasUnappliedConfChanges()]: false, since there is no
    reconfiguration.

    **In scope and unfinished** (2026-09-16).  Blocked on [own_raftLog], and
    the tempting shortcut does not work: the generated body
    ([new/code/go_etcd_io/raft/v3.v:3732]) opens with

        if r.raftLog.applied >= r.raftLog.committed { return false }

    but [applied >= committed] is a fact about the log that nothing available
    implies, so the [scan] over [(applied, committed]] is **genuinely
    reachable** -- it is not dead under our scope.  Returning [false]
    therefore needs [own_raftLog] to say that no entry in that range has
    [Type] [EntryConfChange] or [EntryConfChangeV2], i.e. it needs the entry
    list exposed, which is exactly the design question recorded for
    [own_raftLog] in notes/raft-election-refinement.md. *)
Definition wp_raft__hasUnappliedConfChanges_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (r : loc) l,
  {{{ is_pkg_init raft ∗ own_raftLog l }}}
    r @! (go.PointerType raft.raft) @! "hasUnappliedConfChanges" #()
  {{{ RET #false; own_raftLog l }}}.

Module Type RAFT__HASUNAPPLIEDCONFCHANGES.
  Parameter wp_raft__hasUnappliedConfChanges : wp_raft__hasUnappliedConfChanges_body.
  Arguments wp_raft__hasUnappliedConfChanges {_ _ _ _ _ _ _ _}.
End RAFT__HASUNAPPLIEDCONFCHANGES.
