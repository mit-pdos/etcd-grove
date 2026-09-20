Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_raft_phys.

(** [c.VoteResult(votes)] for a *single* majority quorum.

    This is the arithmetic half of [TallyVotes]: [JointConfig.VoteResult]
    calls it on each of the two components of the joint config
    ([quorum.v:154,158]) and combines the two answers.

    The receiver is a [*MajorityConfig], i.e. a location [cref] holding the
    map value [mref], because the call site indexes the [JointConfig] array
    and takes the address of the element.  The component is described by its
    *id set* [s], and the two shapes a component can have are both allowed:

      - [mref = map.nil] -- the second component of a simple configuration
        ([own_tracker]'s [Hvoters_arr]); the nil map has no keys, so [s = ∅];
      - a real map [mref ↦$ ids] with [dom ids = s].

    The body ([quorum.MajorityConfig__VoteResultⁱᵐᵖˡ], majority.go:170) is

        if len(c) == 0 { return VoteWon }        // "elections on an empty
                                                 //  config win", by convention
        var votedCnt, missing int
        for id := range c {
          v, ok := votes[id]
          if !ok { missing++; continue }
          if v { votedCnt++ }
        }
        q := len(c)/2 + 1
        if votedCnt >= q { return VoteWon }
        if votedCnt+missing >= q { return VotePending }
        return VoteLost

    so [votedCnt = size (granted votes ∩ s)], [missing = size (s ∖ dom votes)]
    and, by [is_quorum_alt] ([inv_tracker.v]), [votedCnt ≥ q] is exactly
    [is_quorum s (granted votes)].  For [VoteLost],
    [votedCnt + missing = size (s ∖ rejected votes)]
    ([size_cfg_minus_rejected]), so [votedCnt + missing < q] is exactly
    [¬ is_quorum s (s ∖ rejected votes)].

    **Why the two [s ≠ ∅] premises.**  At [s = ∅] the function returns
    [VoteWon] without computing anything, while [is_quorum ∅ q] unfolds to
    [0 < 2 * 0], which is [False]; so the [VoteWon] equivalence is simply
    false there, and the empty case is reported separately.  [own_tracker]
    carries [cfg ≠ ∅], which is what lets the caller use the equivalences for
    the first component; the second component *is* empty, and the caller uses
    the [s = ∅] clause for it.

    The size bound is needed because [len], [votedCnt], [missing] and [q] are
    [go.int]: with [size s < 2^63] none of the additions wraps.  Callers get
    it from [own_tracker]'s [Hcfg_size]. *)
Definition wp_MajorityConfig__VoteResult_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (s : gset w64) (cref mref votes_ref : loc) (dq : dfrac)
    (votes : gmap w64 bool),
  {{{ is_pkg_init quorum ∗ ⌜ Z.of_nat (size s) < 2 ^ 63 ⌝ ∗
      cref ↦ mref ∗ votes_ref ↦${dq} votes ∗
      (⌜ mref = map.nil ∧ s = ∅ ⌝ ∨
       ∃ (ids : gmap w64 unit), ⌜ dom ids = s ⌝ ∗ mref ↦$ ids) }}}
    cref @! (go.PointerType quorum.MajorityConfig) @! "VoteResult" #votes_ref
  {{{ (res : w8), RET #res;
      cref ↦ mref ∗ votes_ref ↦${dq} votes ∗
      (⌜ mref = map.nil ∧ s = ∅ ⌝ ∨
       ∃ (ids : gmap w64 unit), ⌜ dom ids = s ⌝ ∗ mref ↦$ ids) ∗
      ⌜ res = VoteWon ∨ res = VoteLost ∨ res = VotePending ⌝ ∗
      ⌜ s = ∅ → res = VoteWon ⌝ ∗
      ⌜ s ≠ ∅ → (res = VoteWon ↔ is_quorum s (granted votes)) ⌝ ∗
      ⌜ s ≠ ∅ → (res = VoteLost ↔ ¬ is_quorum s (s ∖ rejected votes)) ⌝ }}}.

Module Type MAJORITYCONFIG__VOTERESULT.
  Parameter wp_MajorityConfig__VoteResult : wp_MajorityConfig__VoteResult_body.
  Arguments wp_MajorityConfig__VoteResult {_ _ _ _ _ _ _ _}.
End MAJORITYCONFIG__VOTERESULT.
