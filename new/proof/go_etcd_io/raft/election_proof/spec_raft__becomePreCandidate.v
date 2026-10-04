Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [becomePreCandidate] (raft.go:912, 2026-10-04): [r.step :=
    stepCandidate], [r.trk.ResetVotes()], [r.tick], [r.lead := None],
    [r.state := StatePreCandidate], and a log line.  Term and vote are
    untouched and there is no [reset], so the [Progress] values stay
    ([become_precandidate], [defs.v]).  The panic branch ([state =
    StateLeader]) is discharged from the role premise. *)
Definition wp_raft__becomePreCandidate_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64)
    (r : loc) (id : w64) (s : nstate.t),
  s.(nstate.role) ≠ prole.Leader →
  {{{ is_pkg_init raft ∗ own_raft_phys cfg r id s }}}
    r @! (go.PointerType raft.raft) @! "becomePreCandidate" #()
  {{{ RET #(); own_raft_phys cfg r id (become_precandidate s) }}}.

Module Type BECOMEPRECANDIDATE.
  Parameter wp_raft__becomePreCandidate : wp_raft__becomePreCandidate_body.
  Arguments wp_raft__becomePreCandidate {_ _ _ _ _ _ _ _}.
End BECOMEPRECANDIDATE.
