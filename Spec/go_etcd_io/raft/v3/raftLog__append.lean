/-
## `(*raftLog).append(ents ...*pb.Entry) uint64` (internal)

**Users**: `appendEntry` (`raft.go:852`, the leader's proposals at `lastIndex + 1`), `maybeAppend`,
`RawNode.Bootstrap` (`bootstrap.go:63`, on an empty log). Snippet `raftlog/append.go`
(`ReqLeaderAppend`).

**Proof sketch**: empty: `lastIndex`. Else the `Panicf` on `k - 1 < committed` is excluded by the
premise; `unstable.truncateAndAppend` (its premises: `1 ≤ k ≤ offset + |ents|`, no wrap); then
`lastIndex`, which is `end` with unstable entries. `Wf` is kept: the truncation is above
`committed`, so `committed ≤ end`; a truncation below `offset` keeps the stored entries.

**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/raftLog__append.lean`: over `LogState`.

**Margin**: none.
-/
module

public import Spec.go_etcd_io.raft.v3.ApiLog

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

/-- (internal) Append `es` at `k` (truncating the log after `k - 1`), returning the new last index. -/
def raftLog.append.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (sl : GoSlice) (k : Nat) (es : List LogEntry),
  (es = [] ∨ (ls.committed < k ∧ k ≤ ls.us.offset + ls.us.ents.length ∧ k + es.length < 2 ^ 64)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls ∗ entriesRO sl k es }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"append")) (Val #sl))
  {{ (li : w64), RET #li; raftLog l (ls.truncateAppend k es) ∗
      ⌜uint.nat li = (ls.truncateAppend k es).lastIndex⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
