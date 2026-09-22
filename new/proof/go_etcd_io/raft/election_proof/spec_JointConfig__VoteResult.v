Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [c.VoteResult(votes)] for the joint config, i.e. the last statement of
    [TallyVotes].  The receiver is [&r.trk.Config.Voters], the same field ref
    [campaign] passes to [JointConfig.IDs].

    The body ([quorum.JointConfig__VoteResultⁱᵐᵖˡ], joint.go:62) asks each
    component and combines:

        r1 := c[0].VoteResult(votes)
        r2 := c[1].VoteResult(votes)
        if r1 == r2 { return r1 }
        if r1 == VoteLost || r2 == VoteLost { return VoteLost }
        return VotePending

    The configuration here is *simple*, so [own_tracker]'s [Hvoters_arr] says
    the array is [[voters_ref; map.nil]]: the second component is empty and
    [MajorityConfig.VoteResult] answers [VoteWon] for it by convention.  The
    combination then returns [r1] whatever it is -- [VoteWon] through the
    first test, [VoteLost] through the second, [VotePending] through the
    fall-through -- so the joint answer is exactly the answer for [cfg].

    Both conjuncts are equivalences, not implications: nothing here is lost.
    [is_quorum cfg ∅] is [False] at [cfg = ∅], but [own_tracker] carries
    [Hcfg_ne : cfg ≠ ∅] (see [inv_tracker.v] for why it is there and why
    adding it cost nothing), so the empty-config convention never bites. *)
Definition wp_JointConfig__VoteResult_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (trk : loc) tv votes,
  {{{ is_pkg_init quorum ∗ trk ↦ tv ∗ own_tracker cfg tv votes }}}
    (trk.[tracker.ProgressTracker.t, "Config"].[tracker.Config.t, "Voters"])
      @! (go.PointerType quorum.JointConfig) @! "VoteResult"
        #(tv.(tracker.ProgressTracker.Votes'))
  {{{ (res : w8), RET #res;
      trk ↦ tv ∗ own_tracker cfg tv votes ∗
      ⌜ res = VoteWon ∨ res = VoteLost ∨ res = VotePending ⌝ ∗
      ⌜ res = VoteWon ↔ is_quorum cfg (granted votes) ⌝ ∗
      (* [VoteLost] is "cannot still win", not "a majority rejected"; see
         [spec_ProgressTracker__TallyVotes.v] and [election_proof/protocol.v]'s
         [step_lose]. *)
      ⌜ res = VoteLost ↔ ¬ is_quorum cfg (cfg ∖ rejected votes) ⌝ }}}.

Module Type JOINTCONFIG__VOTERESULT.
  Parameter wp_JointConfig__VoteResult : wp_JointConfig__VoteResult_body.
  Arguments wp_JointConfig__VoteResult {_ _ _ _ _ _ _ _}.
End JOINTCONFIG__VOTERESULT.
