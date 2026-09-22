Require Export New.proof.go_etcd_io.raft.election_proof.inv_big.

(** [big.Int.Int64] reads a [big.Int] back as an [int64].

    **Trust boundary.**  [math/big] is not raft and is not translated; the
    method is not even declared in [new/code/math/big.v] (the Goose body of
    [lockedRand.Intn] resolves it by the string ["Int64"]), so
    [etc/check-module-discipline.py] reports it as [F6-unknown-function], a
    warning.  Its only consumer is [lockedRand.Intn], on the assumable RNG
    path.

    Go documents the result as undefined when [x] does not fit an [int64],
    so the triple asks that it does; the implementation then returns exactly
    [x], and [W64 z] read signed is [z] on that range.  The caller has
    [0 ≤ z < n] for a [w64] [n], so the premise is free. *)
Definition wp_big_Int__Int64_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (p : loc) (z : Z),
  - 2 ^ 63 ≤ z < 2 ^ 63 →
  {{{ is_pkg_init big ∗ own_big_Int p z }}}
    p @! (go.PointerType big.Int) @! "Int64" #()
  {{{ RET #(W64 z); own_big_Int p z }}}.

Module Type BIG_INT__INT64.
  Parameter wp_big_Int__Int64 : wp_big_Int__Int64_body.
  Arguments wp_big_Int__Int64 {_ _ _ _ _ _ _ _}.
End BIG_INT__INT64.
