Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** *** Two internal helpers on the way to [BecomeReplicate].

    Stated on [own_inflights] at the exact new value (until 2026-09-23, on
    the raw field points-to).  The ring-buffer invariant survives a reset:
    [start] and [count] go to [0] and the buffer is untouched. *)
Definition wp_Inflights__reset_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (iv : tracker.Inflights.t) (buf : list tracker.inflight.t),
  {{{ is_pkg_init tracker ∗ own_inflights l iv buf }}}
    l @! (go.PointerType tracker.Inflights) @! "reset" #()
  {{{ RET #(); own_inflights l (iv <| tracker.Inflights.start' := W64 0 |>
                                   <| tracker.Inflights.count' := W64 0 |>
                                   <| tracker.Inflights.bytes' := W64 0 |>) buf }}}.

Module Type INFLIGHTS__RESET.
  Parameter wp_Inflights__reset : wp_Inflights__reset_body.
  Arguments wp_Inflights__reset {_ _ _ _ _ _ _ _}.
End INFLIGHTS__RESET.
