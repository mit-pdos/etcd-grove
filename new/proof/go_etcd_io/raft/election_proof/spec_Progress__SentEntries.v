Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.
Require Export New.proof.go_etcd_io.raft.election_proof.spec_Inflights__Full.

(** [pr.SentEntries(entries, bytes)] records a [MsgApp] carrying [entries]
    entries ([Progress__SentEntriesⁱᵐᵖˡ],
    new/code/go_etcd_io/raft/v3/tracker.v:311).  It switches on [pr.State]:

      StateReplicate: Next += entries (if entries > 0), then
                      Inflights.Add(Next-1, bytes), then
                      MsgAppFlowPaused = Inflights.Full()
      StateProbe:     MsgAppFlowPaused = true (if entries > 0)
      otherwise:      panic("sending append in unhandled state %s")

    Hence the two premises.  [state ≠ Snapshot] rules out the panic, and
    the second premise is [Inflights.Add]'s: [Add] panics on a full
    window.  Both are exactly what [maybeSendAppend] has when it gets here
    -- it only reaches this line after [IsPaused()] returned [false] (so
    the state is not Snapshot) and, in [StateReplicate], entries are
    non-empty only when [!pr.Inflights.Full()] was the branch that fetched
    them.

    The new record is [progress_sent_entries p entries bytes] ([defs.v]);
    it leaves [matched] alone (Match discipline,
    notes/raft-replication-model.md).  (Until 2026-10-02 the result was
    existential, with only [Match] pinned.) *)
Definition wp_Progress__SentEntries_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (pr : loc) (p : progress.t) (entries bytes : w64),
  p.(progress.state) ≠ prstate.Snapshot →
  (p.(progress.state) = prstate.Replicate → (0 < sint.Z entries)%Z →
     inflights_full p.(progress.infl) = false) →
  {{{ is_pkg_init tracker ∗ "Hpr" ∷ own_Progress pr p }}}
    pr @! (go.PointerType tracker.Progress) @! "SentEntries" #entries #bytes
  {{{ RET #(); own_Progress pr (progress_sent_entries p entries bytes) }}}.

Module Type PROGRESS__SENTENTRIES.
  Parameter wp_Progress__SentEntries : wp_Progress__SentEntries_body.
  Arguments wp_Progress__SentEntries {_ _ _ _ _ _ _ _}.
End PROGRESS__SENTENTRIES.
