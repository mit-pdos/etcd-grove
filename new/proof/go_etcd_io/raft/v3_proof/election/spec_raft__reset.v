Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [reset term] clears the vote iff the term changes, clears [lead] and the
    vote tally, and re-initializes the non-election state. *)
Definition wp_raft__reset_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64)
    (r : loc) (id : w64) (s : nstate.t) (term : w64) (f : func.t),
  {{{ is_pkg_init raft ∗ own_raft_phys_at cfg r id s f }}}
    r @! (go.PointerType raft.raft) @! "reset" #term
  {{{ RET #();
      (* [f] carried through: [reset] does not touch [r.step], and
         [becomeFollower] calls it while the field and the role disagree --
         see [own_raft_phys_at] in inv_raft_phys.v *)
      own_raft_phys_at cfg r id
        {| nstate.term := term;
           nstate.vote := if decide (term = s.(nstate.term))
                          then s.(nstate.vote) else W64 0;
           nstate.lead := W64 0;
           nstate.role := s.(nstate.role);
           nstate.votes := ∅;
           nstate.outbox := s.(nstate.outbox) |} f }}}.

Module Type RESET.
  Parameter wp_raft__reset : wp_raft__reset_body.
  Arguments wp_raft__reset {_ _ _ _ _ _ _ _}.
End RESET.
