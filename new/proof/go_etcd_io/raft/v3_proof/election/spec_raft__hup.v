(** * Spec: [raft.raft__hup]

    The single place this function's Hoare triple is written down.  The body
    carries all of its own binders, so the [Parameter] is a bare reference to
    it -- there is no second copy of the binder list to drift. *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [hup] checks the node is a promotable voter with no unapplied
    configuration change, then campaigns. *)
Definition wp_raft__hup_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64)
    (γ : raft_election_names) (r : loc) (id : w64) (s : nstate.t) (t : raft.CampaignType.t),
  t ≠ campaignPreElection →
  {{{ is_pkg_init raft ∗
      "Hphys" ∷ own_raft_phys γ r id s ∗
      "Hghost" ∷ own_raft_ghost γ id s
  }}}
    r @! (go.PointerType raft.raft) @! "hup" #t
  {{{ s', RET #();
      own_raft_phys γ r id s' ∗ own_raft_ghost γ id s' ∗
      ⌜ ∃ sent, step cfg id s [] s' sent ⌝ }}}.

Module Type HUP.
  Parameter wp_raft__hup : wp_raft__hup_body.
End HUP.
