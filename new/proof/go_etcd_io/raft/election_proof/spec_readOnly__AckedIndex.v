Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [ro.AckedIndex(voterID)] ([readOnly__AckedIndexⁱᵐᵖˡ],
    new/code/go_etcd_io/raft/v3.v:6286; [read_only.go:72]), the read-only
    object seen as a [quorum.AckedIndexer]:

      idx, found := ro.acks[voterID]
      return quorum.Index(idx), found

    No panic, no call.  The result is the voter's ack in the
    [(value-or-0, ok)] form of [is_AckedIndexer]'s contract
    ([inv_tracker.v]), which is what this triple exists to discharge for
    [maybeAdvance]. *)
Definition wp_readOnly__AckedIndex_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (ro : loc) (r : readonly.t) (voterID : w64),
  {{{ is_pkg_init raft ∗ "Hown" ∷ own_ReadOnly ro r }}}
    ro @! (go.PointerType raft.readOnly) @! "AckedIndex" #voterID
  {{{ RET (#(default (W64 0) (r.(readonly.acks) !! voterID)),
           #(bool_decide (is_Some (r.(readonly.acks) !! voterID))));
      own_ReadOnly ro r }}}.

Module Type READONLY__ACKEDINDEX.
  Parameter wp_readOnly__AckedIndex : wp_readOnly__AckedIndex_body.
  Arguments wp_readOnly__AckedIndex {_ _ _ _ _ _ _ _}.
End READONLY__ACKEDINDEX.
