Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [p.Committed()]: the largest index a quorum of voters has acknowledged
    ([ProgressTracker__Committedⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3/tracker.v:795;
    tracker.go:179):

        return uint64(p.Voters.CommittedIndex(matchAckIndexer(p.Progress)))

    One exit, no panic.  One call, [JointConfig.CommittedIndex] on
    [&p.Config.Voters] with the progress map converted to the
    [quorum.AckedIndexer] interface (Goose:
    [Convert matchAckIndexer quorum.AckedIndexer (![ProgressMap] p.Progress)],
    i.e. [interface.mk_ok tracker.matchAckIndexer #p.Progress]).

    The tracker is unchanged.  The result [N] is [MaxUint64] for an empty
    configuration (never the case for a raft node, whose voter set contains
    itself, but [own_tracker] allows it), and otherwise the quorum index of
    the voters' [Match] ([is_quorum_index], [inv_tracker.v]):

      - [N] is some voter's [Match];
      - [is_quorum cfg (filter (λ v, N ≤ Match v) cfg)] -- a quorum of
        voters have acknowledged [N], in [protocol.v]'s sense of
        [is_quorum] ([size cfg < 2 * size (q ∩ cfg)]);
      - no larger index has such a quorum.

    [pvs_match_at t.(trk.peers) v] is [v]'s [Match] ([0] off the map, which no voter
    is: [own_tracker]'s maps have domain [cfg]). *)
Definition wp_ProgressTracker__Committed_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (trk : loc) tv (t : trk.t),
  {{{ is_pkg_init tracker ∗ trk ↦ tv ∗ own_tracker cfg tv t }}}
    trk @! (go.PointerType tracker.ProgressTracker) @! "Committed" #()
  {{{ (N : w64), RET #N;
      trk ↦ tv ∗ own_tracker cfg tv t ∗
      ⌜ cfg = ∅ → N = W64 (2 ^ 64 - 1) ⌝ ∗
      ⌜ cfg ≠ ∅ → is_quorum_index cfg (pvs_match_at t.(trk.peers)) N ⌝ }}}.

Module Type PROGRESSTRACKER__COMMITTED.
  Parameter wp_ProgressTracker__Committed : wp_ProgressTracker__Committed_body.
  Arguments wp_ProgressTracker__Committed {_ _ _ _ _ _ _ _}.
End PROGRESSTRACKER__COMMITTED.
