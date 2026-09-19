Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [TallyVotes] reports the outcome of the election, which is exactly the
    quorum condition of the model.

    **In scope.  The array half of what blocked this is fixed (2026-09-17);
    a nil-map [len] still blocks it.**
    Everything down to the [Admitted] is machine-checked
    ([rocq compile -vok] over a scratch module holding this identical
    script, RC=0): the whole tally loop over [trk.Progress] is proved, and
    the program is parked on the function's last statement,
    [p.Config.Voters.VoteResult(p.Votes)].

    What *used* to block it is the same array-indexing defect that blocked
    [wp_JointConfig__IDs] ([spec_JointConfig__IDs.v], which has the full
    write-up).  [quorum.JointConfig] is [[2]MajorityConfig], an *array*, and
    Goose translated the element reads [c[0]] / [c[1]] inside
    [JointConfig.VoteResult] as [IndexRef] applied to the array *value*,
    where [index_ref_array] only steps on an array *location*.  **Fixed
    2026-09-17**: the emitted code is now

        MethodResolve (go.PointerType MajorityConfig) "VoteResult"
          (IndexRef JointConfig ("c", #(W64 0)))

    ([new/code/.../quorum.v:154,158]).

    A **second** obstacle remains, and the array fix does not clear it: the
    second component of the joint config is [map.nil] ([Hvoters_arr]), and
    [MajorityConfig.VoteResult] begins with [len(c) == 0].  [go.len_map]
    unfolds to [InternalMapLength (Read "m")] -- at [map.nil] a read of the
    null location -- and there is no nil-map case for [go.len] the way there
    is one for ranging ([wp_map_nil_for_range],
    [new/golang/theory/map.v:305]).  **Now measured** (2026-09-17), where the
    old note said "not probed": [wp_auto] leaves
    [#(functions go.len [go.MapType go.uint64 go.bool]) (#map.nil)]
    completely untouched, so it is stuck rather than awkward.  Filed in
    bugs/golang-len-of-nil-map-is-stuck.md.

    **The [VoteWon] conjunct is false when [cfg = ∅], and that is not fixed
    by unblocking the translation.**  [MajorityConfig.VoteResult] returns
    [VoteWon] outright when [len(c) == 0] ("by convention, the elections on
    an empty config win", [new/code/.../quorum.v:416-418]), while
    [is_quorum ∅ q] unfolds to [0 < 2 * 0], which is [False].  Nothing in
    [own_tracker] rules [cfg = ∅] out: [dom prs = cfg] and [dom voters = cfg]
    are both satisfiable at [∅].  The fix is a [⌜ cfg ≠ ∅ ⌝] conjunct in
    [own_tracker] -- a *strengthening* of a predicate that no proof
    constructs from scratch, so it costs nothing to add and it is preserved
    by every method here -- not a weakening of this statement.  It was left
    undone because the lemma is unprovable anyway and adding it would have
    touched files outside this one's blast radius.

    **What remains once [IndexRef] steps**, in terms of what is already
    proved in [inv_tracker.v]: the joint result is [r1], the
    [MajorityConfig.VoteResult]
    of [voters_ref], because [r2] is the empty config's [VoteWon] and
    [JointConfig.VoteResult] returns [r1] when [r1 = r2], [VoteLost] when
    either is [VoteLost], and [VotePending] otherwise.  In
    [MajorityConfig.VoteResult] over [voters_ref] ([dom voters = cfg]):
    [votedCnt = size (granted votes ∩ cfg)] and
    [missing = size (cfg ∖ dom votes)], each a [wp_map_for_range] with an
    [nsat] invariant exactly like the one in the banked prefix of
    [proof_ProgressTracker__TallyVotes.v], discharged by [nsat_granted]
    and [nsat_missing].  Then [q = size cfg / 2 + 1], so
    [votedCnt ≥ q ↔ is_quorum cfg (granted votes)] by [is_quorum_alt], and
    [votedCnt + missing < q ↔ ¬ is_quorum cfg (cfg ∖ rejected votes)] by
    [is_quorum_alt] together with [size_cfg_minus_rejected].  That is the
    whole of both postcondition conjuncts; the pure half of the argument is
    already machine-checked, in [inv_tracker.v]. *)
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
