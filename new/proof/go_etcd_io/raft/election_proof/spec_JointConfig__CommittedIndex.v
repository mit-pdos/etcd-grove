Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [c.CommittedIndex(l)] for the joint config
    ([quorum.JointConfig__CommittedIndexⁱᵐᵖˡ],
    new/code/go_etcd_io/raft/v3/quorum.v:126; joint.go:50):

        idx0 := c[0].CommittedIndex(l)
        idx1 := c[1].CommittedIndex(l)
        if idx0 < idx1 { return idx0 }               // exit 1
        return idx1                                  // exit 2

    No panic.  Calls: [MajorityConfig.CommittedIndex] twice; the indexer's
    [AckedIndex] is reached from inside it, through the interface, by the
    caller-supplied contract [is_AckedIndexer] ([inv_tracker.v]) -- the
    indexer is arbitrary, with the resource [P] it needs, which comes back.

    (Until 2026-10-04 this was stated for the tracker's receiver and
    indexer only, on [own_tracker].  It is now the general triple, so that
    [readOnly.maybeAdvance] can use it with the read-only object as the
    indexer; [ProgressTracker.Committed] ([proof_ProgressTracker__Committed.v])
    instantiates it at the tracker.)

    The receiver is a [*JointConfig] at [c] (a caller holding a struct
    field passes the field's location), pointing at a simple
    configuration: [a = [m0; nil]], [m0] holding the voters ([dom ids]),
    [c[1]] nil, whose [CommittedIndex] is [MaxUint64] by convention, so
    that [min] picks [c[0]]'s answer on both exits.  The result is
    [MaxUint64] for an empty configuration, and otherwise the quorum index
    of [default 0 (acked v)] over the voters ([is_quorum_index]); a voter
    the indexer does not know counts [0].  The voter map comes back at some
    [ids'] with the same key set (the callee's contract). *)
Definition wp_JointConfig__CommittedIndex_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (c : loc) (a : quorum.JointConfig.t) (m0 : loc) (ids : gmap w64 unit)
    (l : interface.t) (P : iProp Σ) (acked : w64 → option w64),
  {{{ is_pkg_init quorum ∗ ⌜ Z.of_nat (size (dom ids)) < 2 ^ 63 ⌝ ∗
      c ↦ a ∗ ⌜ array.arr a = [m0; map.nil] ⌝ ∗ m0 ↦$ ids ∗
      is_AckedIndexer l P acked ∗ P }}}
    c @! (go.PointerType quorum.JointConfig) @! "CommittedIndex" #l
  {{{ (N : w64), RET #N;
      c ↦ a ∗ (∃ ids' : gmap w64 unit, ⌜ dom ids' = dom ids ⌝ ∗ m0 ↦$ ids') ∗ P ∗
      ⌜ dom ids = ∅ → N = W64 (2 ^ 64 - 1) ⌝ ∗
      ⌜ dom ids ≠ ∅ → is_quorum_index (dom ids) (λ v, default (W64 0) (acked v)) N ⌝ }}}.

Module Type JOINTCONFIG__COMMITTEDINDEX.
  Parameter wp_JointConfig__CommittedIndex : wp_JointConfig__CommittedIndex_body.
  Arguments wp_JointConfig__CommittedIndex {_ _ _ _ _ _ _ _}.
End JOINTCONFIG__COMMITTEDINDEX.
