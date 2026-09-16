Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [campaign] becomes a candidate and broadcasts a vote request to every
    other voter.  Several protocol steps, refining one [step_campaign] — but
    stated here as a pure fact about the resulting state, with no ghost state
    involved: the messages it sends are the growth of the outbox, and whether
    that growth is protocol-legal is [Step]'s problem.

    [peers] is existential because the Go code iterates the voter set in
    whatever order [IDs] yields; [step_campaign] accepts any permutation of
    [elements (cfg ∖ {[id]})]. *)
Definition wp_raft__campaign_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64)
    (r : loc) (id : w64) (s : nstate.t) (t : raft.CampaignType.t),
  t ≠ campaignPreElection →
  s.(nstate.role) ≠ role.Leader →
  id ∈ cfg →
  {{{ is_pkg_init raft ∗ own_raft_phys cfg r id s }}}
    r @! (go.PointerType raft.raft) @! "campaign" #t
  {{{ (peers : list w64), RET #();
      ⌜ peers ≡ₚ elements (cfg ∖ {[id]}) ⌝ ∗
      let s' := become_candidate id s in
      own_raft_phys cfg r id
        (send_msgs s'
           ([msg.mk mtype.VoteResp id id s'.(nstate.term) false] ++
            ((λ to, msg.mk mtype.Vote id to s'.(nstate.term) false) <$> peers))) }}}.

Module Type CAMPAIGN.
  Parameter wp_raft__campaign : wp_raft__campaign_body.
  Arguments wp_raft__campaign {_ _ _ _ _ _ _ _}.
End CAMPAIGN.
