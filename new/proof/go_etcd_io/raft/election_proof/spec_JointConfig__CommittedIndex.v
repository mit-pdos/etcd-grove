Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [c.CommittedIndex(l)] for the joint config, as [ProgressTracker.Committed]
    calls it: the receiver is [&p.Config.Voters] and the indexer is
    [matchAckIndexer(p.Progress)], the tracker's own progress map
    ([quorum.JointConfig__CommittedIndexⁱᵐᵖˡ],
    new/code/go_etcd_io/raft/v3/quorum.v:126; joint.go:50):

        idx0 := c[0].CommittedIndex(l)
        idx1 := c[1].CommittedIndex(l)
        if idx0 < idx1 { return idx0 }               // exit 1
        return idx1                                  // exit 2

    No panic.  Calls: [MajorityConfig.CommittedIndex] twice; the indexer's
    [AckedIndex] is reached from inside it, through the interface, and is
    discharged here from [matchAckIndexer.AckedIndex]'s triple.

    Stated on [own_tracker], like [JointConfig.VoteResult], with the
    indexer argument fixed to the interface value
    [Convert matchAckIndexer AckedIndexer p.Progress] evaluates to
    ([interface.mk_ok tracker.matchAckIndexer #tv.Progress']): the voter
    map ([c[0]]) and the progress map behind the indexer are two parts of
    the same tracker, which is why the indexer is specified on
    [own_progress_map] and not on [own_tracker].

    The configuration is simple ([own_tracker]'s [Hvoters_arr]): [c[1]] is
    nil, its [CommittedIndex] is [MaxUint64] by convention, and [min] picks
    [c[0]]'s answer on both exits.  So the result is
    [MajorityConfig.CommittedIndex]'s for [cfg]: [MaxUint64] if [cfg] is
    empty, and otherwise the quorum index of the voters' [Match]
    ([is_quorum_index], with [pvs_match_at pvs]; every voter has a
    [Progress], [own_tracker] makes the two maps' domains [cfg]). *)
Definition wp_JointConfig__CommittedIndex_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (cfg : gset w64) (trk : loc) tv votes (prs : gmap w64 loc)
    (pvs : gmap w64 (tracker.Progress.t * tracker.Inflights.t)),
  {{{ is_pkg_init quorum ∗ is_pkg_init tracker ∗
      trk ↦ tv ∗ own_tracker cfg tv votes prs pvs }}}
    (trk.[tracker.ProgressTracker.t, "Config"].[tracker.Config.t, "Voters"])
      @! (go.PointerType quorum.JointConfig) @! "CommittedIndex"
        #(interface.mk_ok tracker.matchAckIndexer
            #(tv.(tracker.ProgressTracker.Progress')))
  {{{ (N : w64), RET #N;
      trk ↦ tv ∗ own_tracker cfg tv votes prs pvs ∗
      ⌜ cfg = ∅ → N = W64 (2 ^ 64 - 1) ⌝ ∗
      ⌜ cfg ≠ ∅ → is_quorum_index cfg (pvs_match_at pvs) N ⌝ }}}.

Module Type JOINTCONFIG__COMMITTEDINDEX.
  Parameter wp_JointConfig__CommittedIndex : wp_JointConfig__CommittedIndex_body.
  Arguments wp_JointConfig__CommittedIndex {_ _ _ _ _ _ _ _}.
End JOINTCONFIG__COMMITTEDINDEX.
