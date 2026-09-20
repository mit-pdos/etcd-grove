Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_big.

(** [big.NewInt(x)] allocates a [big.Int] holding [x].

    **Trust boundary.**  [math/big] is not raft and is not translated
    ([new/code/math/big.v] declares only the name [big.NewInt]; there is no
    [NewIntⁱᵐᵖˡ] and no [FuncUnfold] in [big.Assumptions]), so the call cannot
    be stepped and this triple stands in for it.  Its only consumer is
    [lockedRand.Intn], which is on the RNG path the scope rule allows to be
    assumed.  The argument is Go's [int64], i.e. a [w64] read signed. *)
Definition wp_big_NewInt_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (x : w64),
  {{{ is_pkg_init big }}}
    @! big.NewInt #x
  {{{ (p : loc), RET #p; own_big_Int p (sint.Z x) }}}.

Module Type BIG_NEWINT.
  Parameter wp_big_NewInt : wp_big_NewInt_body.
  Arguments wp_big_NewInt {_ _ _ _ _ _ _ _}.
End BIG_NEWINT.
