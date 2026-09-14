(** * Spec: [raft.raft__becomeLeader]

    The single place this function's Hoare triple is written down.  The body
    carries all of its own binders, so the [Parameter] is a bare reference to
    it -- there is no second copy of the binder list to drift. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [becomeLeader] is [reset], the role transition, marking its own
    [Progress] replicating, and the empty entry.  [id ∈ cfg] is needed because
    only voters are in the [Progress] map. *)
Definition wp_raft__becomeLeader_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64)
    (γ : raft_election_names) (r : loc) (id : w64) (s : nstate.t),
  s.(nstate.role) ≠ role.Follower →
  id ∈ cfg →
  {{{ is_pkg_init raft ∗ own_raft_phys γ r id s }}}
    r @! (go.PointerType raft.raft) @! "becomeLeader" #()
  {{{ RET #(); own_raft_phys γ r id (become_leader id s) }}}.

Module Type BECOMELEADER.
  Parameter wp_raft__becomeLeader : wp_raft__becomeLeader_body.
End BECOMELEADER.
