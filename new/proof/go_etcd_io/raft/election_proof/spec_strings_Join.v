Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [strings.Join] is not translated ([new/code/strings.v] declares only the
    name), so this is an [Axiom]: Go's standard library, outside raft.
    [newRaft] uses it only to build a log line; the postcondition is *some*
    string. *)
Definition wp_strings_Join_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (elems : slice.t) (xs : list go_string) (dq : dfrac) (sep : go_string),
  {{{ is_pkg_init strings ∗ elems ↦*{dq} xs }}}
    @! strings.Join #elems #sep
  {{{ (s : go_string), RET #s; elems ↦*{dq} xs }}}.

Module Type STRINGS_JOIN.
  Parameter wp_strings_Join : wp_strings_Join_body.
  Arguments wp_strings_Join {_ _ _ _ _ _ _ _}.
End STRINGS_JOIN.
