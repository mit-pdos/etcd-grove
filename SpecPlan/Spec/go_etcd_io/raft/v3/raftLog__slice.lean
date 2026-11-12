/-
## `(*raftLog).slice(lo, hi, maxSize)` (internal)

**Users**: `entries`, `nextCommittedEnts`, `scan`. Snippet `raftlog/reads.go`.

**Proof sketch**: `mustCheckOutOfBounds` (its `ErrCompacted`); `lo == hi`: `nil`. All unstable:
`limitSize(unstable.slice(lo, hi))`, capped. Else `Storage.Entries(lo, min(hi, offset), maxSize)`
through `isStorage` (`ErrCompacted` returned, below the floor; `ErrUnavailable` impossible: the
storage holds `[σ.off+1, stable]` and `lo` is in it), a non-empty prefix of `stored`'s (the
invariant); if it is short or reaches the size, it is the answer; else the unstable part
(`limitSize`), `entsSize`, and `extend` (allocating: the storage's slice has no spare capacity, R1's
contract, requested; the sum is below `2^63`, the premise).

**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/raftLog__slice.lean`: over `LogState`; the `2^63` premise is new (the old
proof left `extend`'s `len + len` to an unproved bound): the memory limitation of Perennial's slices.

**Margin**: the size limit is not stated.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.ApiLog

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal) A prefix of the entries `[lo, hi)`, non-empty if the range is (or `ErrCompacted`). -/
def raftLog.slice.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (lo hi mx : w64),
  uint.nat lo ≤ uint.nat hi → uint.nat hi ≤ ls.lastIndex + 1 → uint.nat hi - uint.nat lo < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls }}
    (App (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"slice")) (Val #lo)) (Val #hi)) (Val #mx))
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); raftLog l ls ∗
      ((⌜err = interface.nil⌝ ∗ ∃ es, entriesRO sl (uint.nat lo) es ∗
          ⌜es <+: ls.range (uint.nat lo) (uint.nat hi) ∧ (uint.nat lo < uint.nat hi → es ≠ [])⌝) ∨
       (errIs go_etcd_io.raft.v3.ErrCompacted err ∗ ⌜uint.nat lo ≤ ls.compactFloor⌝ ∗ logCompactedLb l (uint.nat lo))) }}

end spec
end Raft
end EtcdGrove
end Perennial
