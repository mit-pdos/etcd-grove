Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [becomeFollower] is [reset] plus assignments to [lead] and [state]; the
    postcondition is literally the model's role transition. *)
Definition wp_raft__becomeFollower_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (γ : raft_election_names) (r : loc) (id : w64) (s : nstate.t) (term lead : w64),
  {{{ is_pkg_init raft ∗ own_raft_phys γ r id s }}}
    r @! (go.PointerType raft.raft) @! "becomeFollower" #term #lead
  {{{ RET #(); own_raft_phys γ r id (become_follower s term lead) }}}.

Module Type BECOMEFOLLOWER.
  Parameter wp_raft__becomeFollower : wp_raft__becomeFollower_body.
End BECOMEFOLLOWER.
