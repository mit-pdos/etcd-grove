Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [NewInflights] allocates one.

    The premise bounds the ring size.  It is what [own_inflights]'s
    ring-buffer invariant ([inflights_ok], [inv_tracker.v]) asks of a fresh
    [Inflights]: a negative [size] would make [0 ≤ len(buffer) ≤ size]
    false, and a [size] at or above [2^62] would let [Inflights.grow]'s
    [len(buffer) * 2] overflow.  The one caller on this path is [reset]'s
    [Visit] closure, passing [r.trk.MaxInflight], which [own_tracker]'s
    [HmaxInfl] bounds.  Added 2026-09-20 with the invariant. *)
Definition wp_tracker_NewInflights_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (size maxBytes : w64),
  (0 ≤ sint.Z size < 2 ^ 62)%Z →
  {{{ is_pkg_init tracker }}}
    @! tracker.NewInflights #size #maxBytes
  {{{ (l : loc), RET #l; own_inflights l }}}.

Module Type TRACKER_NEWINFLIGHTS.
  Parameter wp_tracker_NewInflights : wp_tracker_NewInflights_body.
  Arguments wp_tracker_NewInflights {_ _ _ _ _ _ _ _}.
End TRACKER_NEWINFLIGHTS.
