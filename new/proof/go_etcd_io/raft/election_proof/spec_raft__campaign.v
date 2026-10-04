Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [campaign(t)] becomes a candidate -- or, for [t = campaignPreElection]
    (since 2026-10-04), a pre-candidate -- and broadcasts a vote request to
    every other voter, plus the self-addressed response.  Stated as a pure
    fact about the resulting state, [campaign_state] ([defs.v]), with no
    ghost state involved: the messages it sends are the growth of the
    outbox, and whether that growth is protocol-legal is [Step]'s problem
    ([step_campaign_state], [step_lemmas.v]).

    [peers] is existential because the Go code iterates the voter set in
    whatever order [IDs] yields; [step_campaign] accepts any permutation of
    [elements (cfg ∖ {[id]})].

    [promotable] is checked first and only logged; until 2026-10-04 the
    spec assumed no pending snapshot so that the warning was dead, but
    [stepCandidate]'s pre-vote win calls [campaign] with no such fact at
    hand, so the warning arm is now covered. *)
Definition wp_raft__campaign_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64)
    (r : loc) (id : w64) (s : nstate.t) (t : raft.CampaignType.t),
  s.(nstate.role) ≠ prole.Leader →
  id ∈ cfg →
  (* Every request and the self-addressed response carry [Term + 1]: for
     an election [becomeCandidate] has raised [r.Term] to it, for a
     pre-election it is computed.  [send] *panics* on a vote message whose
     [Term] is zero ([Panicf "term should be set when sending %s"] in
     [raft__sendⁱᵐᵖˡ]), which is why [wp_raft__send] requires [Term ≠ 0].
     Without this premise the triple is **false** at [s.(nstate.term) =
     2^64 - 1]: the term wraps to zero and the real code panics.  Added
     2026-09-16; see notes/STATUS.md. *)
  uint.Z s.(nstate.term) + 1 < 2 ^ 64 →
  {{{ is_pkg_init raft ∗ own_raft_phys cfg r id s }}}
    r @! (go.PointerType raft.raft) @! "campaign" #t
  {{{ (peers : list w64) pvs, RET #();
      ⌜ peers ≡ₚ elements (cfg ∖ {[id]}) ⌝ ∗
      (* each request carries the [lastEntryID()] read just before it was
         built ([Index: last.index, LogTerm: last.term]) -- the log's last
         entry id, the same for every peer: nothing in the loop changes the
         log *)
      own_raft_phys cfg r id
        (campaign_state id s (bool_decide (t = campaignPreElection)) peers
           <| nstate.prvals := pvs |>) }}}.

Module Type CAMPAIGN.
  Parameter wp_raft__campaign : wp_raft__campaign_body.
  Arguments wp_raft__campaign {_ _ _ _ _ _ _ _}.
End CAMPAIGN.
