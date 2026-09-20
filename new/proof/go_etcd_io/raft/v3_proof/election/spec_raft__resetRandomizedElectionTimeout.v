Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [resetRandomizedElectionTimeout] draws from the global RNG and writes
    [r.randomizedElectionTimeout].  The *RNG* is outside core raft and is
    assumed ([spec_rand_Int.v]); this wrapper is raft code, so it is a
    [Lemma].  The field it writes appears in no other conjunct of
    [own_raft_phys], and the model has no clock, so the new value is
    existential.

    [0 < electionTimeout] is not optional.  The body is
    [r.electionTimeout + globalRand.Intn(r.electionTimeout)], and
    [lockedRand.Intn] reaches [crypto/rand.Int], which **panics** on a
    non-positive bound -- so without the premise the triple is false at
    [electionTimeout ≤ 0].  Raft establishes it in [Config.validate]
    ([ElectionTick > HeartbeatTick > 0]) and [own_raft_phys] carries it as
    [HelectionTimeout]; [reset] passes it through.  Added 2026-09-20. *)
Definition wp_raft__resetRandomizedElectionTimeout_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (r : loc) rv,
  0 < sint.Z rv.(raft.raft.electionTimeout') →
  {{{ is_pkg_init raft ∗ r ↦ rv }}}
    r @! (go.PointerType raft.raft) @! "resetRandomizedElectionTimeout" #()
  {{{ (n : w64), RET #();
      r ↦ (rv <| raft.raft.randomizedElectionTimeout' := n |>) }}}.

Module Type RAFT__RESETRANDOMIZEDELECTIONTIMEOUT.
  Parameter wp_raft__resetRandomizedElectionTimeout : wp_raft__resetRandomizedElectionTimeout_body.
  Arguments wp_raft__resetRandomizedElectionTimeout {_ _ _ _ _ _ _ _}.
End RAFT__RESETRANDOMIZEDELECTIONTIMEOUT.
