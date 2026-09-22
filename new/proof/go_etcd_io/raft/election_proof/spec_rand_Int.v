Require Export New.proof.go_etcd_io.raft.election_proof.inv_big.

(** [rand.Int(rand.Reader, max)] -- [crypto/rand] -- returns a uniformly
    random [*big.Int] in [[0, max)] and a [nil] error.

    **Trust boundary.**  This is the RNG behind
    [raft.resetRandomizedElectionTimeout], which notes/STATUS.md lists as
    assumable: it is not raft, and [crypto/rand] is not translated
    ([new/code/crypto/rand.v] declares the name [rand.Int] and nothing
    else), so the call cannot be stepped.

    Two things this triple claims, and why each is the honest reading of the
    Go code rather than a convenience:

    - **[max] must be positive.**  [crypto/rand.Int] begins with
      [if max.Sign() <= 0 { panic("crypto/rand: argument to Int is <= 0") }].
      A triple without the premise would say the call returns on a
      non-positive bound; it does not.  This is what makes
      [lockedRand.Intn] -- and through it [resetRandomizedElectionTimeout]
      -- require [0 < n], and is why [own_raft_phys] carries
      [0 < electionTimeout] (established by [Config.validate]:
      [ElectionTick > HeartbeatTick > 0]).
    - **The error is [nil].**  The reader is pinned to the package's own
      [rand.Reader] (the points-to in the precondition, which
      [is_pkg_init rand] provides): since Go 1.24 [crypto/rand.Reader]
      never returns an error -- [Read] on it crashes the program rather than
      report failure -- and [Int] propagates only the reader's error.  Raft
      relies on the same fact: [lockedRand.Intn] [panic]s on a non-nil
      error, and a proof has to show that path unreachable.
    The result is [0 ≤ z < max]; uniformity is not stated because nothing
    on the election path is about distribution. *)
Definition wp_rand_Int_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (rdr : interface.t) (max : loc) (mz : Z),
  0 < mz →
  {{{ is_pkg_init rand ∗ (global_addr rand.Reader) ↦□ rdr ∗
      own_big_Int max mz }}}
    @! rand.Int #rdr #max
  {{{ (v : loc) (z : Z), RET (#v, #interface.nil);
      own_big_Int max mz ∗ own_big_Int v z ∗ ⌜ 0 ≤ z < mz ⌝ }}}.

Module Type RAND_INT.
  Parameter wp_rand_Int : wp_rand_Int_body.
  Arguments wp_rand_Int {_ _ _ _ _ _ _ _}.
End RAND_INT.
