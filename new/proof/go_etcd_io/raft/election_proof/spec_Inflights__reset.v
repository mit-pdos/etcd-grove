Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [in.reset()] ([Inflights__resetⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3/tracker.v):
    [in.start = 0; in.count = 0; in.bytes = 0].  Called by
    [Progress.ResetState], on the way to [BecomeReplicate] and friends.

    Stated on [own_Inflights] at the exact new record,
    [inflights_reset i] ([defs.v]); [start] is internal.  The ring-buffer
    invariant survives: [start] and [count] go to [0] and the buffer is
    untouched.  (Until 2026-10-02 stated on [own_inflights] at the Goose
    value; until 2026-09-23 on the raw field points-to.) *)
Definition wp_Inflights__reset_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (i : inflights.t),
  {{{ is_pkg_init tracker ∗ own_Inflights l i }}}
    l @! (go.PointerType tracker.Inflights) @! "reset" #()
  {{{ RET #(); own_Inflights l (inflights_reset i) }}}.

Module Type INFLIGHTS__RESET.
  Parameter wp_Inflights__reset : wp_Inflights__reset_body.
  Arguments wp_Inflights__reset {_ _ _ _ _ _ _ _}.
End INFLIGHTS__RESET.
