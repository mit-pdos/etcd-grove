Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** *** Two internal helpers on the way to [BecomeReplicate].

    Both are stated over the *field* points-tos rather than over
    [own_progress] / [own_inflights], because the caller's [wp_auto] has to
    keep stepping through field reads after the call returns and cannot see
    through an opaque predicate (see notes/gotchas.md). *)
Definition wp_Inflights__reset_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (iv : tracker.Inflights.t),
  {{{ is_pkg_init tracker ∗ l ↦ iv }}}
    l @! (go.PointerType tracker.Inflights) @! "reset" #()
  {{{ RET #(); l ↦ (iv <| tracker.Inflights.start' := W64 0 |>
                       <| tracker.Inflights.count' := W64 0 |>
                       <| tracker.Inflights.bytes' := W64 0 |>) }}}.

Module Type INFLIGHTS__RESET.
  Parameter wp_Inflights__reset : wp_Inflights__reset_body.
  Arguments wp_Inflights__reset {_ _ _ _ _ _ _ _}.
End INFLIGHTS__RESET.
