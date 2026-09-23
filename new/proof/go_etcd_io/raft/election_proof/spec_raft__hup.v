Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [hup] checks the node is a promotable voter with no unapplied
    configuration change, then campaigns.  Genuinely disjunctive — it either
    campaigns or returns having done nothing — so unlike [campaign] its
    postcondition names the model's relation rather than a specific state; the
    do-nothing case is [step_refl].

    Ghost-free: the [step] witness is a pure fact handed to the caller, which
    is where it is turned into an update of [own_raft_ghost]. *)
Definition wp_raft__hup_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64)
    (r : loc) (id : w64) (s : nstate.t) (t : raft.CampaignType.t),
  t ≠ campaignPreElection →
  (* [hup] may reach [campaign], which increments the term -- see the note on
     [wp_raft__campaign_body]. *)
  uint.Z s.(nstate.term) + 1 < 2 ^ 64 →
  (* [r.step] matches the role and nothing is on loan; kept by the call *)
  nstate_wf s →
  {{{ is_pkg_init raft ∗ own_raft_phys cfg r id s }}}
    r @! (go.PointerType raft.raft) @! "hup" #t
  {{{ s', RET #();
      own_raft_phys cfg r id s' ∗ ⌜ nstate_wf s' ⌝ ∗
      ⌜ step cfg id (to_pstate s) [] (to_pstate s') ⌝ }}}.

Module Type HUP.
  Parameter wp_raft__hup : wp_raft__hup_body.
  Arguments wp_raft__hup {_ _ _ _ _ _ _ _}.
End HUP.
