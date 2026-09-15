Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [poll] records a vote and reports the tally, tied to the model's quorum
    conditions by [wp_ProgressTracker__TallyVotes]. *)
Definition wp_raft__poll_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64)
    (γ : raft_election_names) (r : loc) (id : w64) (s : nstate.t) (from : w64) (t : w32) (v : bool),
  {{{ is_pkg_init raft ∗ own_raft_phys γ r id s }}}
    r @! (go.PointerType raft.raft) @! "poll" #from #t #v
  {{{ (g rj : w64) (res : w8), RET (#g, #rj, #res);
      let votes' := record_vote s.(nstate.votes) from v in
      own_raft_phys γ r id (s <| nstate.votes := votes' |>) ∗
      ⌜ res = VoteWon ∨ res = VoteLost ∨ res = VotePending ⌝ ∗
      ⌜ res = VoteWon → is_quorum cfg (granted votes') ⌝ ∗
      ⌜ res = VoteLost → is_quorum cfg (rejected votes') ⌝ }}}.

Module Type POLL.
  Parameter wp_raft__poll : wp_raft__poll_body.
  Arguments wp_raft__poll {_ _ _ _ _ _ _ _}.
End POLL.
