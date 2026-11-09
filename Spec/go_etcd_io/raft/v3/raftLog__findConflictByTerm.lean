/-
## `(*raftLog).findConflictByTerm(index, term)` (internal)

**Users**: `stepLeader`'s `MsgAppResp` reject (`raft.go:1519`), `handleAppendEntries`' hint
(`raft.go:1839`). Both use the answer only as a probing hint (liveness). Snippet
`raftlog/reads.go` (`ReqConflictHint`).

**Proof sketch**: a loop down from `index` with `term`: each success is `termOf` (exact), stopping at
the first `≤ term`; an error stops with term 0 (`ErrCompacted` below `compactFloor`, or
`ErrUnavailable` past `lastIndex`, where `termOf` is `none`).

**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/raftLog__findConflictByTerm.lean`: over `LogState`.

**Margin**: an error answer is the storage's compaction or the log's end; the post does not say
which.
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

/-- (internal) The largest index `≤ index` whose term is `≤ term` or unknown, with that term (0 if unknown). -/
def raftLog.findConflictByTerm.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (index term : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls }}
    (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"findConflictByTerm")) (Val #index)) (Val #term))
  {{ (r t : w64), RET (PairV #r #t); raftLog l ls ∗
      ⌜uint.nat r ≤ uint.nat index ∧
       (∀ j, uint.nat r < j → j ≤ uint.nat index →
          ∃ tj, ls.termOf j = some tj ∧ uint.nat term < uint.nat tj) ∧
       ((r = W64 0 ∧ t = W64 0) ∨
        (ls.termOf (uint.nat r) = some t ∧ uint.nat t ≤ uint.nat term) ∨
        (t = W64 0 ∧ (ls.termOf (uint.nat r) = none ∨ uint.nat r < ls.compactFloor)))⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
