/-
## `(*raftLog).term(i)` (internal)

**Users**: `sendAppend`'s `prevTerm` (`raft.go:625`: an error means "send a snapshot"),
`matchTerm`, `findConflictByTerm`, `committedEntryInCurrentTerm` (`raft.go:2070`, through
`zeroTermOnOutOfBounds`), log lines. Snippet `raftlog/reads.go` (`ReqPrevTerm`).

**Proof sketch**: `unstable.maybeTerm` (exact); else `firstIndex`/`lastIndex` and `Storage.Term`
through `isStorage`, its update fired in the log's invariant: below the storage's compaction point
`ErrCompacted` (the point is at most `compactFloor`, the stored snapshot at least it, so
`logCompactedLb (i+1)`), past `lastIndex` `ErrUnavailable`, else the stored term (`stored`'s). Go's
`i + 1` wraps at `2^64 - 1`, answering `ErrCompacted` there.

**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/raftLog__term.lean`: over `LogState`; `ErrCompacted` admitted below the
published floor (concurrent compaction), with `logCompactedLb`.

**Margin**: `ErrCompacted` does not say whether the term was known to the log.
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

/-- (internal) The term of index `i`: known, compacted (below the floor), or past the end. -/
def raftLog.term.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"term")) (Val #i))
  {{ (t : w64) (err : GoInterface), RET (PairV #t #err); raftLog l ls ∗
      ((⌜err = interface.nil ∧ ls.termOf (uint.nat i) = some t⌝) ∨
       (errIs go_etcd_io.raft.v3.ErrCompacted err ∗ ⌜t = W64 0⌝ ∗
          ((⌜uint.nat i < ls.compactFloor⌝ ∗ logCompactedLb l (uint.nat i + 1)) ∨
           ⌜uint.nat i = 2 ^ 64 - 1⌝)) ∨
       (errIs go_etcd_io.raft.v3.ErrUnavailable err ∗ ⌜t = W64 0 ∧ ls.lastIndex < uint.nat i⌝)) }}

end spec
end Raft
end EtcdGrove
end Perennial
