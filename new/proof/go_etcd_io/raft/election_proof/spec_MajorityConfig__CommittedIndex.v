Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [c.CommittedIndex(l)] for a *single* majority quorum
    ([quorum.MajorityConfig__CommittedIndexⁱᵐᵖˡ],
    new/code/go_etcd_io/raft/v3/quorum.v:355; majority.go:121):

        n := len(c)
        if n == 0 { return math.MaxUint64 }           // exit 1
        var stk [7]uint64
        var srt []uint64
        if len(stk) >= n { srt = stk[:n] } else { srt = make([]uint64, n) }
        i := n - 1
        for id := range c {
          if idx, ok := l.AckedIndex(id); ok { srt[i] = uint64(idx); i-- }
        }
        slices.Sort(srt)
        pos := n - (n/2 + 1)
        return Index(srt[pos])                         // exit 2

    **Panics**: the two slice accesses [srt[i]] and [srt[pos]] would panic
    out of range; neither can.  [i] starts at [n-1] and is decremented
    only after a write, at most once per voter, so every write is at
    [n-1-j ≥ 0] with [j] the number of acknowledging voters seen so far
    ([j < n] while a voter is still to come).  [pos ∈ [0, n)] for [n ≥ 1].
    The [go.int] arithmetic does not wrap under [size s < 2^63].  Calls:
    [l.AckedIndex] (dynamic, through the interface: the contract is
    [is_AckedIndexer], [inv_tracker.v]) and [slices.Sort] (axiom,
    [spec_slices_Sort.v] -- whose *sortedness* conjunct is what this
    function needs).

    The receiver is a [*MajorityConfig] at [cref], exactly as for
    [MajorityConfig.VoteResult]: the component is either [map.nil] (then
    [s = ∅]) or an owned map with key set [s].  The indexer [l] owns
    whatever [P] it needs; [P] comes back unchanged.

    The result: [MaxUint64] for an empty config (the convention that makes
    a nil second half of a joint config neutral under [min]), and otherwise
    the **quorum index** of the per-voter values [default 0 (acked v)]
    ([is_quorum_index]): one of the values, acknowledged by a quorum of
    [s], and the largest such.  A voter the indexer does not know counts as
    [0] -- that is the zero the [srt] slot keeps. *)
Definition wp_MajorityConfig__CommittedIndex_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (s : gset w64) (cref mref : loc) (l : interface.t) (P : iProp Σ)
    (acked : w64 → option w64),
  {{{ is_pkg_init quorum ∗ ⌜ Z.of_nat (size s) < 2 ^ 63 ⌝ ∗
      cref ↦ mref ∗
      (⌜ mref = map.nil ∧ s = ∅ ⌝ ∨
       ∃ (ids : gmap w64 unit), ⌜ dom ids = s ⌝ ∗ mref ↦$ ids) ∗
      is_AckedIndexer l P acked ∗ P }}}
    cref @! (go.PointerType quorum.MajorityConfig) @! "CommittedIndex" #l
  {{{ (N : w64), RET #N;
      cref ↦ mref ∗
      (⌜ mref = map.nil ∧ s = ∅ ⌝ ∨
       ∃ (ids : gmap w64 unit), ⌜ dom ids = s ⌝ ∗ mref ↦$ ids) ∗
      P ∗
      ⌜ s = ∅ → N = W64 (2 ^ 64 - 1) ⌝ ∗
      ⌜ s ≠ ∅ → is_quorum_index s (λ v, default (W64 0) (acked v)) N ⌝ }}}.

Module Type MAJORITYCONFIG__COMMITTEDINDEX.
  Parameter wp_MajorityConfig__CommittedIndex : wp_MajorityConfig__CommittedIndex_body.
  Arguments wp_MajorityConfig__CommittedIndex {_ _ _ _ _ _ _ _}.
End MAJORITYCONFIG__COMMITTEDINDEX.
