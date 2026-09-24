Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [IsEmptyHardState st] is [st == emptyState], and [emptyState] is the
    zero [HardState] ([is_initialized], [v3_proof/base.v]). *)
Definition wp_IsEmptyHardState_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (st : raftpb.HardState.t),
  {{{ is_pkg_init raft }}}
    @! raft.IsEmptyHardState #st
  {{{ RET #(bool_decide (st.(raftpb.HardState.Term') = W64 0 ∧
                        st.(raftpb.HardState.Vote') = W64 0 ∧
                        st.(raftpb.HardState.Commit') = W64 0));
      True }}}.

Module Type ISEMPTYHARDSTATE.
  Parameter wp_IsEmptyHardState : wp_IsEmptyHardState_body.
  Arguments wp_IsEmptyHardState {_ _ _ _ _ _ _ _}.
End ISEMPTYHARDSTATE.
