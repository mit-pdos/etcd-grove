Require Export New.proof.go_etcd_io.raft.election_proof.inv_big.

(** [lockedRand.Intn(n)] is raft's wrapper around [crypto/rand]: under
    [r.mu] it draws [rand.Int(rand.Reader, big.NewInt(int64(n)))], panics if
    that errs, and returns the draw as an [int].  Raft code, so a [Lemma];
    what it stands on ([big.NewInt], [rand.Int], [big.Int.Int64]) is the
    assumed RNG path -- see [spec_rand_Int.v].

    [0 < n] is not optional: [rand.Int] panics on a non-positive bound
    ([spec_rand_Int.v]), and so, therefore, does [Intn].  The postcondition
    is the bound the caller ([resetRandomizedElectionTimeout]) does not need
    but [rand.Int] gives for free. *)
Definition wp_lockedRand__Intn_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (lr : loc) (n : w64),
  0 < sint.Z n →
  {{{ is_pkg_init raft ∗ is_lockedRand lr }}}
    lr @! (go.PointerType raft.lockedRand) @! "Intn" #n
  {{{ (v : w64), RET #v; ⌜ 0 ≤ sint.Z v < sint.Z n ⌝ }}}.

Module Type LOCKEDRAND__INTN.
  Parameter wp_lockedRand__Intn : wp_lockedRand__Intn_body.
  Arguments wp_lockedRand__Intn {_ _ _ _ _ _ _ _}.
End LOCKEDRAND__INTN.
