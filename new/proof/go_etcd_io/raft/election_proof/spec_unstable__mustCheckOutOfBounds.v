Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [u.mustCheckOutOfBounds(lo, hi)]: panics unless
    [u.offset <= lo <= hi <= u.offset + len(u.entries)].

    Both [Panicf] calls have to be shown unreachable, since
    [wp_Logger__logf] does not cover them; that is what the range premise
    is for.  The no-wrap premise is what lets [offset + len(entries)] be
    computed without overflow.  On a bare [*unstable] with the entry slice
    beside it, like the [maybe*] specs; any fraction, since it only reads
    the slice's length. *)
Definition wp_unstable__mustCheckOutOfBounds_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (u : loc) (uv : raft.unstable.t) (uents : list raftpb.Entry.t)
      (lo hi : w64),
  (uint.Z uv.(raft.unstable.offset') ≤ uint.Z lo ≤ uint.Z hi ≤
   uint.Z uv.(raft.unstable.offset') + Z.of_nat (length uents))%Z →
  (uint.Z uv.(raft.unstable.offset') + Z.of_nat (length uents) < 2^64)%Z →
  {{{ is_pkg_init raft ∗ "Hun" ∷ own_unstable u uv uents None }}}
    u @! (go.PointerType raft.unstable) @! "mustCheckOutOfBounds" #lo #hi
  {{{ RET #(); own_unstable u uv uents None }}}.

Module Type UNSTABLE__MUSTCHECKOUTOFBOUNDS.
  Parameter wp_unstable__mustCheckOutOfBounds : wp_unstable__mustCheckOutOfBounds_body.
  Arguments wp_unstable__mustCheckOutOfBounds {_ _ _ _ _ _ _ _}.
End UNSTABLE__MUSTCHECKOUTOFBOUNDS.
