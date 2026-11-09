/-
## `(*raftLog).maybeCommit(at)` (internal)

**Users**: `raft.maybeCommit` (`raft.go:796`: the quorum's match index at the leader's term).
**Proof sketch**: `matchTerm(at)` is exact above `committed ≥ compactFloor`; `commitTo` (no panic:
a matched index is at most `lastIndex`). **Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/raftLog__maybeCommit.lean`.
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

/-- (internal) Commit through `at` if it is past `committed`, of a non-zero term, and in the log. -/
def raftLog.maybeCommit.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (aid : go_etcd_io.raft.v3.entryID),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"maybeCommit")) (Val #aid))
  {{ (r : Bool), RET #r;
      ⌜r = decide (aid.term' ≠ W64 0 ∧ ls.committed < uint.nat aid.index' ∧
        ls.termOf (uint.nat aid.index') = some aid.term')⌝ ∗
      raftLog l (if r then { ls with committed := uint.nat aid.index' } else ls) }}

end spec
end Raft
end EtcdGrove
end Perennial
