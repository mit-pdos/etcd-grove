Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [l.appliedTo(i, size)] advances [applied] to [i].  It [Panicf]s unless
    [applied ≤ i ≤ committed], hence the premise; the [applying*] fields it
    also writes are not part of [logstate.t]. *)
Definition wp_raftLog__appliedTo_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (l : loc) (ls : logstate.t) (i size : w64),
  (uint.Z ls.(logstate.applied) ≤ uint.Z i ≤ uint.Z ls.(logstate.committed))%Z →
  {{{ is_pkg_init raft ∗ own_raftLog l ls }}}
    l @! (go.PointerType raft.raftLog) @! "appliedTo" #i #size
  {{{ RET #(); own_raftLog l (ls <| logstate.applied := i |>) }}}.

Module Type RAFTLOG__APPLIEDTO.
  Parameter wp_raftLog__appliedTo : wp_raftLog__appliedTo_body.
  Arguments wp_raftLog__appliedTo {_ _ _ _ _ _ _ _}.
End RAFTLOG__APPLIEDTO.
