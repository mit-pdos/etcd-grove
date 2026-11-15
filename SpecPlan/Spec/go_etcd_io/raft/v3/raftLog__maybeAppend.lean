/-
## `(*raftLog).maybeAppend(a logSlice, committed uint64)` (internal)

**Users**: `handleAppendEntries` (`raft.go:1815`), after its early return for `a.prev.index <
committed`. Snippet `raftlog/append.go` (`ReqFollowerAppend`).

**Proof sketch**: `matchTerm(a.prev)` (exact: `prev ≥ committed ≥ compactFloor`, no compaction
answer); `findConflict` gives `conflict`; the `Panicf` on a conflict at or below `committed` is
excluded by the premise (the caller's log matching: a leader's entries after a matching `prev`
agree with the committed prefix); `append` of the suffix (`k > committed`, `k ≤ end + 1` since
`conflict` stops at the first new index); `commitTo(min(c, lastnewi))`, `lastnewi ≤ lastIndex`
since every entry matched or was appended.

**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/raftLog__maybeAppend.lean`: over `LogState` (`appendFrom`).

**Margin**: none.
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

/-- (internal) Append a leader's entries after `prev`, if `prev` matches, and commit up to the leader's commit index. -/
def raftLog.maybeAppend.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (a : go_etcd_io.raft.v3.logSlice) (es : List LogEntry) (c : w64),
  ls.committed ≤ uint.nat a.prev'.index' →
  uint.nat a.prev'.index' + es.length < 2 ^ 64 →
  (ls.termOf (uint.nat a.prev'.index') = some a.prev'.term' →
    ∀ j, j < es.length → uint.nat a.prev'.index' + 1 + j ≤ ls.committed →
      ls.termOf (uint.nat a.prev'.index' + 1 + j) = (es[j]?).map (·.term)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls ∗ entriesRO a.entries' (uint.nat a.prev'.index' + 1) es ∗
      (⌜sint.Z a.entries'.len = sint.Z a.entries'.cap⌝ ∨ ownSliceCap Loc a.entries' (DFrac.own 1)) }}
    (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"maybeAppend")) (Val #a)) (Val #c))
  {{ (lastnewi : w64) (ok : Bool), RET (PairV #lastnewi #ok);
      ⌜ok = decide (ls.termOf (uint.nat a.prev'.index') = some a.prev'.term')⌝ ∗
      (if ok then ⌜uint.nat lastnewi = uint.nat a.prev'.index' + es.length⌝ ∗
          raftLog l (ls.appendFrom (uint.nat a.prev'.index') es (uint.nat c))
       else ⌜lastnewi = W64 0⌝ ∗ raftLog l ls) }}

end spec
end Raft
end EtcdGrove
end Perennial
