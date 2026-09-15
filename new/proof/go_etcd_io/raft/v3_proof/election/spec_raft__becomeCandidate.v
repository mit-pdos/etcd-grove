Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [becomeCandidate] is [reset] plus the role transition; the panic branch
    ([state = StateLeader]) is discharged from the role hypothesis. *)
Definition wp_raft__becomeCandidate_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (γ : raft_election_names) (r : loc) (id : w64) (s : nstate.t),
  s.(nstate.role) ≠ role.Leader →
  {{{ is_pkg_init raft ∗ own_raft_phys γ r id s }}}
    r @! (go.PointerType raft.raft) @! "becomeCandidate" #()
  {{{ RET #(); own_raft_phys γ r id (become_candidate id s) }}}.

Module Type BECOMECANDIDATE.
  Parameter wp_raft__becomeCandidate : wp_raft__becomeCandidate_body.
End BECOMECANDIDATE.
