Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [id] is one of the two reserved local targets, [LocalAppendThread =
    MaxUint64] and [LocalApplyThread = MaxUint64 - 1]. *)
Definition wp_IsLocalMsgTarget_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (id : w64),
  {{{ is_pkg_init raft }}}
    @! raft.IsLocalMsgTarget #id
  {{{ RET #(bool_decide (id = W64 18446744073709551615 ∨
                         id = W64 18446744073709551614)); True }}}.

Module Type ISLOCALMSGTARGET.
  Parameter wp_IsLocalMsgTarget : wp_IsLocalMsgTarget_body.
  Arguments wp_IsLocalMsgTarget {_ _ _ _ _ _ _ _}.
End ISLOCALMSGTARGET.
