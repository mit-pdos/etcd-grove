Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [TallyVotes] reports the outcome of the election, which is exactly the
    quorum condition of the model.

    **Proved 2026-09-20** ([proof_ProgressTracker__TallyVotes.v]).  The
    function counts the granted and rejected votes over [trk.Progress] and
    then delegates the verdict to
    [p.Config.Voters.VoteResult(p.Votes)]
    ([spec_JointConfig__VoteResult.v] and, under it,
    [spec_MajorityConfig__VoteResult.v]), which is where the quorum
    arithmetic lives.  What the loop here contributes is the two counters,
    and they are *not* what the postcondition talks about: the returned
    [g]/[rj] are existentially quantified, since no caller reads them
    ([poll] returns them to [stepCandidate], which only looks at [res]).

    Three things had to be fixed before this could be proved, all recorded
    here because each cost a day:

    - **Array indexing.**  [quorum.JointConfig] is [[2]MajorityConfig], and
      Goose translated [c[0]] as [IndexRef] applied to the array *value*,
      where [index_ref_array] only steps on an array *location*.  Fixed in
      Goose 2026-09-17; see [spec_JointConfig__IDs.v] for the write-up.

    - **[len] of a nil map.**  The second component of a simple
      configuration is [map.nil], and [MajorityConfig.VoteResult] begins with
      [len(c) == 0].  [pure_wp_map_nil_len] ([new/golang/theory/map.v])
      handles it; the [go.len_underlying] detour a map of a *named* type
      needs is in [proof_MajorityConfig__VoteResult_helpers/majority_len.v].

    The [VoteWon] conjunct is false at [cfg = ∅] -- [MajorityConfig.VoteResult]
    returns [VoteWon] outright for an empty config ("by convention, the
    elections on an empty config win"), while [is_quorum ∅ q] unfolds to
    [0 < 2 * 0].  That is why [own_tracker] carries [Hcfg_ne : cfg ≠ ∅]; see
    [inv_tracker.v] for why adding it cost nothing. *)
Definition wp_ProgressTracker__TallyVotes_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (trk : loc) tv votes,
  {{{ is_pkg_init tracker ∗ trk ↦ tv ∗ own_tracker cfg tv votes }}}
    trk @! (go.PointerType tracker.ProgressTracker) @! "TallyVotes" #()
  {{{ (g rj : w64) (res : w8), RET (#g, #rj, #res);
      trk ↦ tv ∗ own_tracker cfg tv votes ∗
      ⌜ res = VoteWon ∨ res = VoteLost ∨ res = VotePending ⌝ ∗
      ⌜ res = VoteWon → is_quorum cfg (granted votes) ⌝ ∗
      (* [VoteLost] means the candidate **cannot still win**, not that a
         majority rejected -- Go computes [votedCnt + missing < q], and
         [votedCnt + missing = size (cfg ∖ rejected)].  The old form,
         [is_quorum cfg (rejected votes)], was false: 4 voters with 2
         rejecting and 2 silent gives [VoteLost] with no rejection quorum.
         Corrected 2026-09-16; see election_protocol.v's [step_lose]. *)
      ⌜ res = VoteLost → ¬ is_quorum cfg (cfg ∖ rejected votes) ⌝ }}}.

Module Type PROGRESSTRACKER__TALLYVOTES.
  Parameter wp_ProgressTracker__TallyVotes : wp_ProgressTracker__TallyVotes_body.
  Arguments wp_ProgressTracker__TallyVotes {_ _ _ _ _ _ _ _}.
End PROGRESSTRACKER__TALLYVOTES.
