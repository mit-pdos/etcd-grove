Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** Field-wise equality of two [HardState]s; [HardState] has exactly the
    three fields compared. *)
Definition wp_isHardStateEqual_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (a b : raftpb.HardState.t),
  {{{ is_pkg_init raft }}}
    @! raft.isHardStateEqual #a #b
  {{{ RET #(bool_decide (a.(raftpb.HardState.Term') = b.(raftpb.HardState.Term') ∧
                        a.(raftpb.HardState.Vote') = b.(raftpb.HardState.Vote') ∧
                        a.(raftpb.HardState.Commit') = b.(raftpb.HardState.Commit')));
      True }}}.

Module Type ISHARDSTATEEQUAL.
  Parameter wp_isHardStateEqual : wp_isHardStateEqual_body.
  Arguments wp_isHardStateEqual {_ _ _ _ _ _ _ _}.
End ISHARDSTATEEQUAL.
