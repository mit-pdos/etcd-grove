/-
Port of `election_proof/spec_readOnly__maybeAdvance.v` (feb5c73d4).

Lean notes:
* `readonly.t` is `ReadOnly`, `own_ReadOnly`/`own_readreq` are `ownReadOnly`/
  `ownReadreq`, `readonly_advance` is `readonlyAdvance` (`InvMisc.lean`);
  `is_quorum_index` is `IsQuorumIndex` (`InvTracker.lean`).
* `default (W64 0) (r.acks !! v)` is `(r.acks !! v).getD (W64 0)`; `array.arr c` is
  `c.arr`; `size (dom ids)` is `GMap.size (domSet ids)`; `length r.pending`, at `Z`, is
  `(r.pending.length : Int)`.
* Rocq's `[∗ list] p; q ∈ ptrs; L, P` is `[∗list] _k ↦ p;q ∈ ptrs;L, P`.
-/
import EtcdGrove.Raft.InvRaftPhys

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `ro.maybeAdvance(c)` (`readOnly.maybeAdvance.impl`,
`EtcdRaft/Code/go_etcd_io/raft/v3.lean`; Rocq new/code/go_etcd_io/raft/v3.v:6303;
`read_only.go:79`):

    newConfirmedReads := uint64(c.CommittedIndex(ro))     // ro as AckedIndexer
    if newConfirmedReads <= ro.confirmedReads { return nil }
    readStates := ro.unconfirmedReads[:newConfirmedReads-ro.confirmedReads]
    ro.unconfirmedReads = ro.unconfirmedReads[newConfirmedReads-ro.confirmedReads:]
    ro.confirmedReads = newConfirmedReads
    return readStates

The configuration `c` is passed by value: `c[0]` is the voter map `m0` (`ids`), `c[1]`
is nil (a simple configuration, as `ownTracker`'s). The quorum index `N` of the voters'
acknowledged positions (`IsQuorumIndex`, over `r.acks`; unknown voters count `0`) is
how many requests have ever been confirmed; `readonlyAdvance r N` (`InvMisc.lean`) is
the new record and the confirmed requests, which are removed from the front of the
queue.

**The result aliases the queue.** `readStates` is the dropped prefix of
`unconfirmedReads`'s backing array and keeps its capacity
(`notes/raft-implementation-facts.md`, "Which slices raft hands out uncapped"): an
`append` to it would overwrite live reads. The spec hands it out **read-only, for
good**: `sl ↦*□ ptrs`, with the requests it points at (`ownReadreq`, persistent) in the
same order as the confirmed records, and *no* `ownSliceCap` -- the slack past `sl`'s
length is `ro`'s own. (No loan to return: nothing is ever written to the prefix again,
so there is nothing to hand back.) The caller (`stepLeader`) only ranges over it. When
nothing is confirmed the result is `nil`, which satisfies the same triple with
`ptrs = []`.

**Panics.** The two reslices panic when `N - confirmedReads` exceeds the queue's
length; and `N = MaxUint64` for an empty voter set. Both are excluded only by what the
*caller* knows -- that every voter's ack is a position the leader actually sent
(`≤ confirmed + len pending`; a forged heartbeat context breaks this in real raft) and
that the voter set is non-empty -- so they are premises (`Hne`, `Hbound`) here, the
smallest that rule it out. (`Hsz` is `MajorityConfig.CommittedIndex`'s.) The voter map
`m0` is lent to `CommittedIndex` and comes back at some map with the same key set. -/
abbrev readOnly.maybeAdvance.spec : Prop :=
  ∀ (ro : Loc) (r : ReadOnly) (c : quorum.JointConfig) (m0 : Loc)
    (ids : GMap w64 Unit),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hown" ∷ ownReadOnly ro r ∗
      "%Hc" ∷ ⌜c.arr = [m0, map.nil]⌝ ∗
      "Hvoters" ∷ m0 ↦$ ids ∗
      "%Hsz" ∷ ⌜(GMap.size (domSet ids) : Int) ≤ 2 ^ 62⌝ ∗
      "%Hne" ∷ ⌜domSet ids ≠ ∅⌝ ∗
      "%Hbound" ∷ ⌜∀ v, v ∈ domSet ids →
          uint.Z ((r.acks !! v).getD (W64 0))
            ≤ uint.Z r.confirmed + (r.pending.length : Int)⌝ }}
    (App (Val (ro @!! go.GoType.PointerType readOnly.ty @!! go!"maybeAdvance")) (Val #c))
  {{ (sl : GoSlice) (N : w64), RET #sl;
      ⌜IsQuorumIndex (domSet ids) (fun v => (r.acks !! v).getD (W64 0)) N⌝ ∗
      ownReadOnly ro (readonlyAdvance r N).1 ∗
      (∃ ids' : GMap w64 Unit, ⌜domSet ids' = domSet ids⌝ ∗ m0 ↦$ ids') ∗
      (∃ ptrs : List Loc, sl ↦*□ ptrs ∗
         [∗list] _k ↦ p;q ∈ ptrs;(readonlyAdvance r N).2, ownReadreq p q) }}

end spec

end EtcdGrove
end Perennial
