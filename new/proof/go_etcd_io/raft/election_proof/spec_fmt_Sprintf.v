Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [fmt.Sprintf] is not translated ([new/code/fmt.v] declares only the
    name), so this is an [Axiom]: Go's standard library, outside raft.
    [newRaft] uses it only to build a log line.  The postcondition is
    *some* string: nothing reads what it says.

    Like [fmt.Errorf]'s triple ([new/proof/fmt.v]) it does not ask that
    each argument be formattable; [newRaft] passes only [uint64]s. *)
Definition wp_fmt_Sprintf_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (format : go_string) (args : slice.t) (xs : list interface.t) (dq : dfrac),
  {{{ is_pkg_init fmt ∗ args ↦*{dq} xs }}}
    @! fmt.Sprintf #format #args
  {{{ (s : go_string), RET #s; args ↦*{dq} xs }}}.

Module Type FMT_SPRINTF.
  Parameter wp_fmt_Sprintf : wp_fmt_Sprintf_body.
  Arguments wp_fmt_Sprintf {_ _ _ _ _ _ _ _}.
End FMT_SPRINTF.
