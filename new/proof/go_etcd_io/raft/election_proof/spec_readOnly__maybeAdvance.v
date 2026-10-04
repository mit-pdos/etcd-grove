Require Export New.proof.go_etcd_io.raft.election_proof.inv_raft_phys.

(** [ro.maybeAdvance(c)] ([readOnly__maybeAdvanceⁱᵐᵖˡ],
    new/code/go_etcd_io/raft/v3.v:6303; [read_only.go:79]):

      newConfirmedReads := uint64(c.CommittedIndex(ro))     // ro as AckedIndexer
      if newConfirmedReads <= ro.confirmedReads { return nil }
      readStates := ro.unconfirmedReads[:newConfirmedReads-ro.confirmedReads]
      ro.unconfirmedReads = ro.unconfirmedReads[newConfirmedReads-ro.confirmedReads:]
      ro.confirmedReads = newConfirmedReads
      return readStates

    The configuration [c] is passed by value: [c[0]] is the voter map [m0]
    ([ids]), [c[1]] is nil (a simple configuration, as [own_tracker]'s).
    The quorum index [N] of the voters' acknowledged positions
    ([is_quorum_index], over [r.acks]; unknown voters count [0]) is how
    many requests have ever been confirmed; [readonly_advance r N]
    ([defs] in [inv_misc.v]) is the new record and the confirmed requests,
    which are removed from the front of the queue.

    **The result aliases the queue.**  [readStates] is the dropped prefix
    of [unconfirmedReads]'s backing array and keeps its capacity
    ([notes/raft-implementation-facts.md], "Which slices raft hands out
    uncapped"): an [append] to it would overwrite live reads.  The spec
    hands it out **read-only, for good**: [sl ↦*□ ptrs], with the
    requests it points at ([own_readreq], persistent) in the same order as
    the confirmed records, and *no* [own_slice_cap] -- the slack past
    [sl]'s length is [ro]'s own.  (No loan to return: nothing is ever
    written to the prefix again, so there is nothing to hand back.)  The
    caller ([stepLeader]) only ranges over it.  When nothing is confirmed
    the result is [nil], which satisfies the same triple with [ptrs = []].

    **Panics.**  The two reslices panic when [N - confirmedReads] exceeds
    the queue's length; and [N = MaxUint64] for an empty voter set.  Both
    are excluded only by what the *caller* knows -- that every voter's ack
    is a position the leader actually sent ([≤ confirmed + len pending];
    a forged heartbeat context breaks this in real raft) and that the
    voter set is non-empty -- so they are premises ([Hne], [Hbound]) here,
    the smallest that rule it out.  ([Hsz] is [MajorityConfig.
    CommittedIndex]'s.)  The voter map [m0] is lent to [CommittedIndex]
    and comes back at some map with the same key set. *)
Definition wp_readOnly__maybeAdvance_body :=
  ∀ (ext : ffi_syntax) (ffi : ffi_model) (ffi_interp0 : ffi_interp ffi)
    (Σ : gFunctors) (hG : heapGS Σ) (ffi_semantics0 : ffi_semantics ext ffi)
    (sem : go.Semantics) (package_sem : raft.Assumptions)
    (ro : loc) (r : readonly.t) (c : quorum.JointConfig.t) (m0 : loc)
    (ids : gmap w64 unit),
  {{{ is_pkg_init raft ∗ "Hown" ∷ own_ReadOnly ro r ∗
      "%Hc" ∷ ⌜ array.arr c = [m0; map.nil] ⌝ ∗
      "Hvoters" ∷ m0 ↦$ ids ∗
      "%Hsz" ∷ ⌜ Z.of_nat (size (dom ids)) < 2 ^ 63 ⌝ ∗
      "%Hne" ∷ ⌜ dom ids ≠ ∅ ⌝ ∗
      "%Hbound" ∷ ⌜ ∀ v, v ∈ dom ids →
          uint.Z (default (W64 0) (r.(readonly.acks) !! v))
            ≤ uint.Z r.(readonly.confirmed) + length r.(readonly.pending) ⌝ }}}
    ro @! (go.PointerType raft.readOnly) @! "maybeAdvance" #c
  {{{ (sl : slice.t) (N : w64), RET #sl;
      ⌜ is_quorum_index (dom ids) (λ v, default (W64 0) (r.(readonly.acks) !! v)) N ⌝ ∗
      own_ReadOnly ro (readonly_advance r N).1 ∗
      (∃ ids' : gmap w64 unit, ⌜ dom ids' = dom ids ⌝ ∗ m0 ↦$ ids') ∗
      (∃ ptrs : list loc, sl ↦*□ ptrs ∗
         [∗ list] p; q ∈ ptrs; (readonly_advance r N).2, own_readreq p q) }}}.

Module Type READONLY__MAYBEADVANCE.
  Parameter wp_readOnly__maybeAdvance : wp_readOnly__maybeAdvance_body.
  Arguments wp_readOnly__maybeAdvance {_ _ _ _ _ _ _ _}.
End READONLY__MAYBEADVANCE.
