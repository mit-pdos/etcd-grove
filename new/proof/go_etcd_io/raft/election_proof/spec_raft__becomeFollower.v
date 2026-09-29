Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [becomeFollower] is [r.step := stepFollower], [reset], and assignments
    to [lead] and [state]; [become_follower] ([defs.v]) is exactly that,
    [r.step] included.  The precondition says nothing about [r.step]: the
    function overwrites it first, which is why [newRaft] can call this on a
    struct whose [step] is still nil. *)
Definition wp_raft__becomeFollower_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64)
    (r : loc) (id : w64) (s : nstate.t) (term lead : w64),
  {{{ is_pkg_init raft ∗ own_raft_phys cfg r id s }}}
    r @! (go.PointerType raft.raft) @! "becomeFollower" #term #lead
  {{{ pvs, RET #(); own_raft_phys cfg r id (become_follower s term lead <| nstate.prvals := pvs |>) }}}.

Module Type BECOMEFOLLOWER.
  Parameter wp_raft__becomeFollower : wp_raft__becomeFollower_body.
  Arguments wp_raft__becomeFollower {_ _ _ _ _ _ _ _}.
End BECOMEFOLLOWER.
