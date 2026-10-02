Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [l.AckedIndex(id)] for [l : matchAckIndexer], the progress map seen as
    a [quorum.AckedIndexer]
    ([matchAckIndexer__AckedIndexⁱᵐᵖˡ], new/code/go_etcd_io/raft/v3/tracker.v:775;
    tracker.go:169):

        pr, ok := l[id]
        if !ok { return 0, false }                    // exit 1
        return quorum.Index(pr.Match), true           // exit 2

    No panic, no call.  The receiver is the map itself ([matchAckIndexer]
    is a named [map[uint64]*Progress]), so the triple is stated on
    [own_progress_map] ([inv_tracker.v]) -- the progress map with the
    [Progress] objects it points at -- not on the tracker: see that
    definition for why.  The result is [pvs_acked pvs id] in the
    [(value-or-0, ok)] form of [is_AckedIndexer]'s contract, which is what
    this triple exists to discharge. *)
Definition wp_matchAckIndexer__AckedIndex_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (mref : loc) (prs : gmap w64 loc)
    (pvs : gmap w64 progress.t) (id : w64),
  {{{ is_pkg_init tracker ∗ own_progress_map mref prs pvs }}}
    mref @! tracker.matchAckIndexer @! "AckedIndex" #id
  {{{ RET (#(default (W64 0) (pvs_acked pvs id)),
           #(bool_decide (is_Some (pvs_acked pvs id))));
      own_progress_map mref prs pvs }}}.

Module Type MATCHACKINDEXER__ACKEDINDEX.
  Parameter wp_matchAckIndexer__AckedIndex : wp_matchAckIndexer__AckedIndex_body.
  Arguments wp_matchAckIndexer__AckedIndex {_ _ _ _ _ _ _ _}.
End MATCHACKINDEXER__ACKEDINDEX.
