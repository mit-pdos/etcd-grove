/-
## `(*raftLog).matchTerm(id)` (internal)

**Users**: `maybeAppend`, `findConflict`, `maybeCommit`, `restore`'s fast-forward
(`raft.go:1928`). **Proof sketch**: `term`. **Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/raftLog__matchTerm.lean`.
**Margin**: `false` below the floor may be a compaction.
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

/-- (internal) Whether the log has `id` (an index below the compaction floor may answer `false`). -/
def raftLog.matchTerm.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (id : go_etcd_io.raft.v3.entryID),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"matchTerm")) (Val #id))
  {{ (r : Bool), RET #r; raftLog l ls ∗
      ⌜(r = true → ls.termOf (uint.nat id.index') = some id.term') ∧
       (r = false → ls.termOf (uint.nat id.index') ≠ some id.term' ∨
          uint.nat id.index' < ls.compactFloor)⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
